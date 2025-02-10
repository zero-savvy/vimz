// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.7.0 <0.9.0;

/*
    Sonobe's Nova + CycleFold decider verifier.
    Joint effort by 0xPARC & PSE.

    More details at https://github.com/privacy-scaling-explorations/sonobe
    Usage and design documentation at https://privacy-scaling-explorations.github.io/sonobe-docs/

    Uses the https://github.com/iden3/snarkjs/blob/master/templates/verifier_groth16.sol.ejs
    Groth16 verifier implementation and a KZG10 Solidity template adapted from
    https://github.com/weijiekoh/libkzg.
    Additionally we implement the NovaDecider contract, which combines the
    Groth16 and KZG10 verifiers to verify the zkSNARK proofs coming from
    Nova+CycleFold folding.
*/


/* =============================== */
/* KZG10 verifier methods */
/**
 * @author  Privacy and Scaling Explorations team - pse.dev
 * @dev     Contains utility functions for ops in BN254; in G_1 mostly.
 * @notice  Forked from https://github.com/weijiekoh/libkzg.
 * Among others, a few of the changes we did on this fork were:
 * - Templating the pragma version
 * - Removing type wrappers and use uints instead
 * - Performing changes on arg types
 * - Update some of the `require` statements 
 * - Use the bn254 scalar field instead of checking for overflow on the babyjub prime
 * - In batch checking, we compute auxiliary polynomials and their commitments at the same time.
 */
contract KZG10Verifier {

    // prime of field F_p over which y^2 = x^3 + 3 is defined
    uint256 public constant BN254_PRIME_FIELD =
        21888242871839275222246405745257275088696311157297823662689037894645226208583;
    uint256 public constant BN254_SCALAR_FIELD =
        21888242871839275222246405745257275088548364400416034343698204186575808495617;

    /**
     * @notice  Performs scalar multiplication in G_1.
     * @param   p  G_1 point to multiply
     * @param   s  Scalar to multiply by
     * @return  r  G_1 point p multiplied by scalar s
     */
    function mulScalar(uint256[2] memory p, uint256 s) internal view returns (uint256[2] memory r) {
        uint256[3] memory input;
        input[0] = p[0];
        input[1] = p[1];
        input[2] = s;
        bool success;
        assembly {
            success := staticcall(sub(gas(), 2000), 7, input, 0x60, r, 0x40)
            switch success
            case 0 { invalid() }
        }
        require(success, "bn254: scalar mul failed");
    }

    /**
     * @notice  Negates a point in G_1.
     * @param   p  G_1 point to negate
     * @return  uint256[2]  G_1 point -p
     */
    function negate(uint256[2] memory p) internal pure returns (uint256[2] memory) {
        if (p[0] == 0 && p[1] == 0) {
            return p;
        }
        return [p[0], BN254_PRIME_FIELD - (p[1] % BN254_PRIME_FIELD)];
    }

    /**
     * @notice  Adds two points in G_1.
     * @param   p1  G_1 point 1
     * @param   p2  G_1 point 2
     * @return  r  G_1 point p1 + p2
     */
    function add(uint256[2] memory p1, uint256[2] memory p2) internal view returns (uint256[2] memory r) {
        bool success;
        uint256[4] memory input = [p1[0], p1[1], p2[0], p2[1]];
        assembly {
            success := staticcall(sub(gas(), 2000), 6, input, 0x80, r, 0x40)
            switch success
            case 0 { invalid() }
        }

        require(success, "bn254: point add failed");
    }

    /**
     * @notice  Computes the pairing check e(p1, p2) * e(p3, p4) == 1
     * @dev     Note that G_2 points a*i + b are encoded as two elements of F_p, (a, b)
     * @param   a_1  G_1 point 1
     * @param   a_2  G_2 point 1
     * @param   b_1  G_1 point 2
     * @param   b_2  G_2 point 2
     * @return  result  true if pairing check is successful
     */
    function pairing(uint256[2] memory a_1, uint256[2][2] memory a_2, uint256[2] memory b_1, uint256[2][2] memory b_2)
        internal
        view
        returns (bool result)
    {
        uint256[12] memory input = [
            a_1[0],
            a_1[1],
            a_2[0][1], // imaginary part first
            a_2[0][0],
            a_2[1][1], // imaginary part first
            a_2[1][0],
            b_1[0],
            b_1[1],
            b_2[0][1], // imaginary part first
            b_2[0][0],
            b_2[1][1], // imaginary part first
            b_2[1][0]
        ];

        uint256[1] memory out;
        bool success;

        assembly {
            success := staticcall(sub(gas(), 2000), 8, input, 0x180, out, 0x20)
            switch success
            case 0 { invalid() }
        }

        require(success, "bn254: pairing failed");

        return out[0] == 1;
    }

    uint256[2] G_1 = [
            1252302219057750281079546250360058346790129148942052154957780403643827152646,
            19881888863336789843490345079244038969461913798614909546488564454647597755672
    ];
    uint256[2][2] G_2 = [
        [
            5984814046337637259138595850753941645650205353415678030179971246871170268852,
            17421167588022607635957355352483062416571351876412304518890850958970456861772
        ],
        [
            14136300277941305665562293229661400391922901229664283823555310692755573474148,
            9554426986436631179788741184421427577625256886197665791309553789393926848751
        ]
    ];
    uint256[2][2] VK = [
        [
            9694460854333325828150719535529628190289577373387819720344562406094413593045,
            19446806910398988525187137733815318273676585977627462623275481633678950607076
        ],
        [
            8051247052812072257992342451641850838124988937453175246641429207432617572637,
            18773176963332085537970872867827319324310393461848486159366121243595208266710
        ]
    ];

    

    /**
     * @notice  Verifies a single point evaluation proof. Function name follows `ark-poly`.
     * @dev     To avoid ops in G_2, we slightly tweak how the verification is done.
     * @param   c  G_1 point commitment to polynomial.
     * @param   pi G_1 point proof.
     * @param   x  Value to prove evaluation of polynomial at.
     * @param   y  Evaluation poly(x).
     * @return  result Indicates if KZG proof is correct.
     */
    function check(uint256[2] calldata c, uint256[2] calldata pi, uint256 x, uint256 y)
        public
        view
        returns (bool result)
    {
        //
        // we want to:
        //      1. avoid gas intensive ops in G2
        //      2. format the pairing check in line with what the evm opcode expects.
        //
        // we can do this by tweaking the KZG check to be:
        //
        //          e(pi, vk - x * g2) = e(c - y * g1, g2) [initial check]
        //          e(pi, vk - x * g2) * e(c - y * g1, g2)^{-1} = 1
        //          e(pi, vk - x * g2) * e(-c + y * g1, g2) = 1 [bilinearity of pairing for all subsequent steps]
        //          e(pi, vk) * e(pi, -x * g2) * e(-c + y * g1, g2) = 1
        //          e(pi, vk) * e(-x * pi, g2) * e(-c + y * g1, g2) = 1
        //          e(pi, vk) * e(x * -pi - c + y * g1, g2) = 1 [done]
        //                        |_   rhs_pairing  _|
        //
        uint256[2] memory rhs_pairing =
            add(mulScalar(negate(pi), x), add(negate(c), mulScalar(G_1, y)));
        return pairing(pi, VK, rhs_pairing, G_2);
    }

    function evalPolyAt(uint256[] memory _coefficients, uint256 _index) public pure returns (uint256) {
        uint256 m = BN254_SCALAR_FIELD;
        uint256 result = 0;
        uint256 powerOfX = 1;

        for (uint256 i = 0; i < _coefficients.length; i++) {
            uint256 coeff = _coefficients[i];
            assembly {
                result := addmod(result, mulmod(powerOfX, coeff, m), m)
                powerOfX := mulmod(powerOfX, _index, m)
            }
        }
        return result;
    }

    
}

/* =============================== */
/* Groth16 verifier methods */
/*
    Copyright 2021 0KIMS association.

    * `solidity-verifiers` added comment
        This file is a template built out of [snarkJS](https://github.com/iden3/snarkjs) groth16 verifier.
        See the original ejs template [here](https://github.com/iden3/snarkjs/blob/master/templates/verifier_groth16.sol.ejs)
    *

    snarkJS is a free software: you can redistribute it and/or modify it
    under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    snarkJS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
    License for more details.

    You should have received a copy of the GNU General Public License
    along with snarkJS. If not, see <https://www.gnu.org/licenses/>.
*/

contract Groth16Verifier {
    // Scalar field size
    uint256 constant r    = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    // Base field size
    uint256 constant q   = 21888242871839275222246405745257275088696311157297823662689037894645226208583;

    // Verification Key data
    uint256 constant alphax  = 1709107232583430745323445604485125874551621915698082929880614745054561964923;
    uint256 constant alphay  = 741295011165911486812947894910050694392365726749052090136895172359920204852;
    uint256 constant betax1  = 2687235582229156165480878264899095079961394516843956609326970804038660771949;
    uint256 constant betax2  = 1930752200766159164959614435002842341490836358701897713628967083550008557702;
    uint256 constant betay1  = 6369461420698254789365148674707651951769509786459033498218178622520538815114;
    uint256 constant betay2  = 2257814670607176513115366080750458513025797830123912604366191412516698020143;
    uint256 constant gammax1 = 15764746416010735386241828026820643256385758017669564007348773220918815691072;
    uint256 constant gammax2 = 5931043219069669962261535212667850473018077206480340092437664729438827930834;
    uint256 constant gammay1 = 21301629265465289459612711012465391284432796359505461463566402931302558021290;
    uint256 constant gammay2 = 1116980474954160208251693266879064799280619158374928856210932554529660378510;
    uint256 constant deltax1 = 19314730364406492787584404173868508412492265131234582340530415437728675096243;
    uint256 constant deltax2 = 13828026598983387060515022153932586255752605882073317420335515654937837691847;
    uint256 constant deltay1 = 11948628007016152799523170657643288164841127603384112035488595796254627851889;
    uint256 constant deltay2 = 12405045336355436915843269399291164503091284725763222739498550314629644644403;

    
    uint256 constant IC0x = 10286249318346505375111759101996674973976122961240859134080454772398500766334;
    uint256 constant IC0y = 13330379486398078570754259433732680791694661790506166294702563336462487437485;
    
    uint256 constant IC1x = 16010388845671969586509744120954471812944352626835988754595090569799829877037;
    uint256 constant IC1y = 3900691435876557179567731369020547895473044909331306136598528407454950117754;
    
    uint256 constant IC2x = 3872661287411717672800137008211975247884824499607524528014249559186394246907;
    uint256 constant IC2y = 4333148671828475846491540193432826561569694247396859316582955931669164674313;
    
    uint256 constant IC3x = 1724438761988476049441761115029156158579422435962958156539057777656424271863;
    uint256 constant IC3y = 10797111245172644043840441737256641074465662455375073543643344002941291288518;
    
    uint256 constant IC4x = 6751350632554754183631651450787987161551071308213744023479590071733880384155;
    uint256 constant IC4y = 8249183607278539339352214264052404215344572560761269428460670502507839764144;
    
    uint256 constant IC5x = 9914158374537919425994740719650605340370342782152001702783298909349470380728;
    uint256 constant IC5y = 12966285718558413384804618357050966450219627566425109127191232220839815143222;
    
    uint256 constant IC6x = 11030855273478488955188090661902931575442726539874773793968156167014696649022;
    uint256 constant IC6y = 901247299507024709393220611410086979283950608972582765048565352458606999893;
    
    uint256 constant IC7x = 7887094119382350930243702656331336680680092332846082854011150423920385293846;
    uint256 constant IC7y = 3990192617244613622664724844114976631326899748922907948840477091113463739629;
    
    uint256 constant IC8x = 7836922384043158142745159362225609161708879876779340150817302535925038547973;
    uint256 constant IC8y = 21242099190310788506077506759186636869703437133288863341701586609546496473809;
    
    uint256 constant IC9x = 11137652694218378591344704925906853347826971970115711242637612970560526347042;
    uint256 constant IC9y = 11748904050940943142358986810163365445796206535051446085751061735187787690183;
    
    uint256 constant IC10x = 17932133121994507256532797065572947902724933537302039082098073688736757201279;
    uint256 constant IC10y = 7536099912815524126307216646397456691353149431592878412127798403813277978204;
    
    uint256 constant IC11x = 7995789262673169127755607616630495629789916630114552241266705548798058757408;
    uint256 constant IC11y = 1705706108195432035208047948053129149327931188734531446299113387251682300449;
    
    uint256 constant IC12x = 11856595363446041938106903110679843201306003372882469608496241689364826555608;
    uint256 constant IC12y = 11535117113931646495493392253187059022144683812905786536839003723820669268953;
    
    uint256 constant IC13x = 21429878686853016381484888720814392311312537940625022568341352939113294584024;
    uint256 constant IC13y = 15037949849320089519344878567233707974055566733770545558538785883693751425232;
    
    uint256 constant IC14x = 3708048752678784168395270215880253446585605635998357634260289346113985321748;
    uint256 constant IC14y = 7425284367601858295817681736857767637250184223661717945011150608622212663148;
    
    uint256 constant IC15x = 288838225409717122231231871026941416581848472352958456340548290875892167345;
    uint256 constant IC15y = 12633872690266214693018417714646533968065198705886904510897925506595375028206;
    
    uint256 constant IC16x = 10146960628697482216540179853166102215558990524234047004390231643093290034611;
    uint256 constant IC16y = 2368655020835808410340482489538879617204202893050524836734611990669855762687;
    
    uint256 constant IC17x = 10033116108756228053974085702613932032284239123075812069522125281232124841059;
    uint256 constant IC17y = 2552357120002839941258614387782052675116568616725462921826772320739526835062;
    
    uint256 constant IC18x = 308777059037286789148245836897076301661474903388457625632692176507443371491;
    uint256 constant IC18y = 12412819686863380449570455719777103302318223484840999193001515222751369236295;
    
    uint256 constant IC19x = 20382100582526089000163781934987345577451410777609435466664484537977345580412;
    uint256 constant IC19y = 2182406763268456714280509868513780836226101314259166283018369446149091540709;
    
    uint256 constant IC20x = 12281915687897061040792563674631889359381203461922331711485068370907908728140;
    uint256 constant IC20y = 1792289794967718465174725061205756936538780069606803558858680095728314595963;
    
    uint256 constant IC21x = 5959138336224722913877973789535460731261860182242342058072657293509675501116;
    uint256 constant IC21y = 13060561719881679518469154497393889542215877351461959824789118007435927232982;
    
    uint256 constant IC22x = 6674721435011343889580752418701280237874551804770847132691392722379144918403;
    uint256 constant IC22y = 2262438342376332092028325578518244750838166657635672896402204457555591900137;
    
    uint256 constant IC23x = 3762606533269448022845805442757399238896685745551581489959789095252208136714;
    uint256 constant IC23y = 10886141508377922821413003628431264028014931908417292575841241444072096851981;
    
    uint256 constant IC24x = 18437720266980959178077396149756599998281972212138728545864266114937975968930;
    uint256 constant IC24y = 16343400076838278607004224152655539900055700728912496069618434907643509695946;
    
    uint256 constant IC25x = 9502008896324098636528078044765632291368524944833292919993792461053781102974;
    uint256 constant IC25y = 12484120661215119809907048219752181110902369508752612477850975525479549816239;
    
    uint256 constant IC26x = 6084820707348160086404073379461341468171343489888379208386280861191366892590;
    uint256 constant IC26y = 18510332086683079554092723864270551987274728708129875362743466755353958676600;
    
    uint256 constant IC27x = 21387349871741258855959164979532701164513716789405553444158471884133900160919;
    uint256 constant IC27y = 19105901607632117593379881280214698361465135044600384779359140926131385571561;
    
    uint256 constant IC28x = 6875080376007818852117403818187670896949742437291636959051552915450072912222;
    uint256 constant IC28y = 4590794086358447431336335904572264074908708647788625516385046976231880521862;
    
    uint256 constant IC29x = 20626170914989349442526410245585674992925964815921741298023231510092753893629;
    uint256 constant IC29y = 17514716970045747964175829859303017855371994585038826669618204948282915331792;
    
    uint256 constant IC30x = 11843102811242120104444882001094435617526906912372429510963098013780042687526;
    uint256 constant IC30y = 5621907022112417684844543773686516812924103691473549866615215660488515344542;
    
    uint256 constant IC31x = 3369064040908666223054921217319793632929935297711133879938128375140254648729;
    uint256 constant IC31y = 4768971275775003259729852541681584457718933099458619624601473933952883963178;
    
    uint256 constant IC32x = 12222435791084035313966177080511289630575503828214275010752262639481479593245;
    uint256 constant IC32y = 19104477375533986743845490390920464809705052875221177904448561825997299238530;
    
    uint256 constant IC33x = 3782720990674590819469402054818445035008495871710145848957303777654432259717;
    uint256 constant IC33y = 7731649218352661333999523289730576190977386499958234455872487796404245581717;
    
    uint256 constant IC34x = 10320469633678725139861852013429534027687285464279678438884091602730575918703;
    uint256 constant IC34y = 15257309321128037929871944611798290898503488734455838948236446562969227817213;
    
    uint256 constant IC35x = 8450311456132023681990713166655892938040222380702587628959860109186308830689;
    uint256 constant IC35y = 14958376864685787563146333236695295845165587284928929521715290391041690746197;
    
    uint256 constant IC36x = 7068728111252302238139900002109019398805198165664618972548252481207136145410;
    uint256 constant IC36y = 8960837315748061119065745535536425045453210813963536460401008556478348124073;
    
    uint256 constant IC37x = 21108260428671896196567968248447280188972802262441611078882607626745239333348;
    uint256 constant IC37y = 14026430853077124964346701454484691703200055977282681635356591361085768048971;
    
    uint256 constant IC38x = 7755442082559593198229418997386727226632687001583669222194633637402253750082;
    uint256 constant IC38y = 15303993734092091549141573512903018879792892283840956138404904324909338638867;
    
    
    // Memory data
    uint16 constant pVk = 0;
    uint16 constant pPairing = 128;

    uint16 constant pLastMem = 896;

    function verifyProof(uint[2] calldata _pA, uint[2][2] calldata _pB, uint[2] calldata _pC, uint[38] calldata _pubSignals) public view returns (bool) {
        assembly {
            function checkField(v) {
                if iszero(lt(v, r)) {
                    mstore(0, 0)
                    return(0, 0x20)
                }
            }
            
            // G1 function to multiply a G1 value(x,y) to value in an address
            function g1_mulAccC(pR, x, y, s) {
                let success
                let mIn := mload(0x40)
                mstore(mIn, x)
                mstore(add(mIn, 32), y)
                mstore(add(mIn, 64), s)

                success := staticcall(sub(gas(), 2000), 7, mIn, 96, mIn, 64)

                if iszero(success) {
                    mstore(0, 0)
                    return(0, 0x20)
                }

                mstore(add(mIn, 64), mload(pR))
                mstore(add(mIn, 96), mload(add(pR, 32)))

                success := staticcall(sub(gas(), 2000), 6, mIn, 128, pR, 64)

                if iszero(success) {
                    mstore(0, 0)
                    return(0, 0x20)
                }
            }

            function checkPairing(pA, pB, pC, pubSignals, pMem) -> isOk {
                let _pPairing := add(pMem, pPairing)
                let _pVk := add(pMem, pVk)

                mstore(_pVk, IC0x)
                mstore(add(_pVk, 32), IC0y)

                // Compute the linear combination vk_x
                
                
                g1_mulAccC(_pVk, IC1x, IC1y, calldataload(add(pubSignals, 0)))
                g1_mulAccC(_pVk, IC2x, IC2y, calldataload(add(pubSignals, 32)))
                g1_mulAccC(_pVk, IC3x, IC3y, calldataload(add(pubSignals, 64)))
                g1_mulAccC(_pVk, IC4x, IC4y, calldataload(add(pubSignals, 96)))
                g1_mulAccC(_pVk, IC5x, IC5y, calldataload(add(pubSignals, 128)))
                g1_mulAccC(_pVk, IC6x, IC6y, calldataload(add(pubSignals, 160)))
                g1_mulAccC(_pVk, IC7x, IC7y, calldataload(add(pubSignals, 192)))
                g1_mulAccC(_pVk, IC8x, IC8y, calldataload(add(pubSignals, 224)))
                g1_mulAccC(_pVk, IC9x, IC9y, calldataload(add(pubSignals, 256)))
                g1_mulAccC(_pVk, IC10x, IC10y, calldataload(add(pubSignals, 288)))
                g1_mulAccC(_pVk, IC11x, IC11y, calldataload(add(pubSignals, 320)))
                g1_mulAccC(_pVk, IC12x, IC12y, calldataload(add(pubSignals, 352)))
                g1_mulAccC(_pVk, IC13x, IC13y, calldataload(add(pubSignals, 384)))
                g1_mulAccC(_pVk, IC14x, IC14y, calldataload(add(pubSignals, 416)))
                g1_mulAccC(_pVk, IC15x, IC15y, calldataload(add(pubSignals, 448)))
                g1_mulAccC(_pVk, IC16x, IC16y, calldataload(add(pubSignals, 480)))
                g1_mulAccC(_pVk, IC17x, IC17y, calldataload(add(pubSignals, 512)))
                g1_mulAccC(_pVk, IC18x, IC18y, calldataload(add(pubSignals, 544)))
                g1_mulAccC(_pVk, IC19x, IC19y, calldataload(add(pubSignals, 576)))
                g1_mulAccC(_pVk, IC20x, IC20y, calldataload(add(pubSignals, 608)))
                g1_mulAccC(_pVk, IC21x, IC21y, calldataload(add(pubSignals, 640)))
                g1_mulAccC(_pVk, IC22x, IC22y, calldataload(add(pubSignals, 672)))
                g1_mulAccC(_pVk, IC23x, IC23y, calldataload(add(pubSignals, 704)))
                g1_mulAccC(_pVk, IC24x, IC24y, calldataload(add(pubSignals, 736)))
                g1_mulAccC(_pVk, IC25x, IC25y, calldataload(add(pubSignals, 768)))
                g1_mulAccC(_pVk, IC26x, IC26y, calldataload(add(pubSignals, 800)))
                g1_mulAccC(_pVk, IC27x, IC27y, calldataload(add(pubSignals, 832)))
                g1_mulAccC(_pVk, IC28x, IC28y, calldataload(add(pubSignals, 864)))
                g1_mulAccC(_pVk, IC29x, IC29y, calldataload(add(pubSignals, 896)))
                g1_mulAccC(_pVk, IC30x, IC30y, calldataload(add(pubSignals, 928)))
                g1_mulAccC(_pVk, IC31x, IC31y, calldataload(add(pubSignals, 960)))
                g1_mulAccC(_pVk, IC32x, IC32y, calldataload(add(pubSignals, 992)))
                g1_mulAccC(_pVk, IC33x, IC33y, calldataload(add(pubSignals, 1024)))
                g1_mulAccC(_pVk, IC34x, IC34y, calldataload(add(pubSignals, 1056)))
                g1_mulAccC(_pVk, IC35x, IC35y, calldataload(add(pubSignals, 1088)))
                g1_mulAccC(_pVk, IC36x, IC36y, calldataload(add(pubSignals, 1120)))
                g1_mulAccC(_pVk, IC37x, IC37y, calldataload(add(pubSignals, 1152)))
                g1_mulAccC(_pVk, IC38x, IC38y, calldataload(add(pubSignals, 1184)))

                // -A
                mstore(_pPairing, calldataload(pA))
                mstore(add(_pPairing, 32), mod(sub(q, calldataload(add(pA, 32))), q))

                // B
                mstore(add(_pPairing, 64), calldataload(pB))
                mstore(add(_pPairing, 96), calldataload(add(pB, 32)))
                mstore(add(_pPairing, 128), calldataload(add(pB, 64)))
                mstore(add(_pPairing, 160), calldataload(add(pB, 96)))

                // alpha1
                mstore(add(_pPairing, 192), alphax)
                mstore(add(_pPairing, 224), alphay)

                // beta2
                mstore(add(_pPairing, 256), betax1)
                mstore(add(_pPairing, 288), betax2)
                mstore(add(_pPairing, 320), betay1)
                mstore(add(_pPairing, 352), betay2)

                // vk_x
                mstore(add(_pPairing, 384), mload(add(pMem, pVk)))
                mstore(add(_pPairing, 416), mload(add(pMem, add(pVk, 32))))


                // gamma2
                mstore(add(_pPairing, 448), gammax1)
                mstore(add(_pPairing, 480), gammax2)
                mstore(add(_pPairing, 512), gammay1)
                mstore(add(_pPairing, 544), gammay2)

                // C
                mstore(add(_pPairing, 576), calldataload(pC))
                mstore(add(_pPairing, 608), calldataload(add(pC, 32)))

                // delta2
                mstore(add(_pPairing, 640), deltax1)
                mstore(add(_pPairing, 672), deltax2)
                mstore(add(_pPairing, 704), deltay1)
                mstore(add(_pPairing, 736), deltay2)


                let success := staticcall(sub(gas(), 2000), 8, _pPairing, 768, _pPairing, 0x20)

                isOk := and(success, mload(_pPairing))
            }

            let pMem := mload(0x40)
            mstore(0x40, add(pMem, pLastMem))

            // Validate that all evaluations ∈ F
            
            checkField(calldataload(add(_pubSignals, 0)))
            
            checkField(calldataload(add(_pubSignals, 32)))
            
            checkField(calldataload(add(_pubSignals, 64)))
            
            checkField(calldataload(add(_pubSignals, 96)))
            
            checkField(calldataload(add(_pubSignals, 128)))
            
            checkField(calldataload(add(_pubSignals, 160)))
            
            checkField(calldataload(add(_pubSignals, 192)))
            
            checkField(calldataload(add(_pubSignals, 224)))
            
            checkField(calldataload(add(_pubSignals, 256)))
            
            checkField(calldataload(add(_pubSignals, 288)))
            
            checkField(calldataload(add(_pubSignals, 320)))
            
            checkField(calldataload(add(_pubSignals, 352)))
            
            checkField(calldataload(add(_pubSignals, 384)))
            
            checkField(calldataload(add(_pubSignals, 416)))
            
            checkField(calldataload(add(_pubSignals, 448)))
            
            checkField(calldataload(add(_pubSignals, 480)))
            
            checkField(calldataload(add(_pubSignals, 512)))
            
            checkField(calldataload(add(_pubSignals, 544)))
            
            checkField(calldataload(add(_pubSignals, 576)))
            
            checkField(calldataload(add(_pubSignals, 608)))
            
            checkField(calldataload(add(_pubSignals, 640)))
            
            checkField(calldataload(add(_pubSignals, 672)))
            
            checkField(calldataload(add(_pubSignals, 704)))
            
            checkField(calldataload(add(_pubSignals, 736)))
            
            checkField(calldataload(add(_pubSignals, 768)))
            
            checkField(calldataload(add(_pubSignals, 800)))
            
            checkField(calldataload(add(_pubSignals, 832)))
            
            checkField(calldataload(add(_pubSignals, 864)))
            
            checkField(calldataload(add(_pubSignals, 896)))
            
            checkField(calldataload(add(_pubSignals, 928)))
            
            checkField(calldataload(add(_pubSignals, 960)))
            
            checkField(calldataload(add(_pubSignals, 992)))
            
            checkField(calldataload(add(_pubSignals, 1024)))
            
            checkField(calldataload(add(_pubSignals, 1056)))
            
            checkField(calldataload(add(_pubSignals, 1088)))
            
            checkField(calldataload(add(_pubSignals, 1120)))
            
            checkField(calldataload(add(_pubSignals, 1152)))
            
            checkField(calldataload(add(_pubSignals, 1184)))
            
            checkField(calldataload(add(_pubSignals, 1216)))
            

            // Validate all evaluations
            let isValid := checkPairing(_pA, _pB, _pC, _pubSignals, pMem)

            mstore(0, isValid)
            
            return(0, 0x20)
        }
    }
}


/* =============================== */
/* Nova+CycleFold Decider verifier */
/**
 * @notice  Computes the decomposition of a `uint256` into num_limbs limbs of bits_per_limb bits each.
 * @dev     Compatible with sonobe::folding-schemes::folding::circuits::nonnative::nonnative_field_to_field_elements.
 */
library LimbsDecomposition {
    function decompose(uint256 x) internal pure returns (uint256[5] memory) {
        uint256[5] memory limbs;
        for (uint8 i = 0; i < 5; i++) {
            limbs[i] = (x >> (55 * i)) & ((1 << 55) - 1);
        }
        return limbs;
    }
}

/**
 * @author  PSE & 0xPARC
 * @title   NovaDecider contract, for verifying Nova IVC SNARK proofs.
 * @dev     This is an askama template which, when templated, features a Groth16 and KZG10 verifiers from which this contract inherits.
 */
contract NovaDecider is Groth16Verifier, KZG10Verifier {
    /**
     * @notice  Computes the linear combination of a and b with r as the coefficient.
     * @dev     All ops are done mod the BN254 scalar field prime
     */
    function rlc(uint256 a, uint256 r, uint256 b) internal pure returns (uint256 result) {
        assembly {
            result := addmod(a, mulmod(r, b, BN254_SCALAR_FIELD), BN254_SCALAR_FIELD)
        }
    }

    /**
     * @notice  Verifies a nova cyclefold proof consisting of two KZG proofs and of a groth16 proof.
     * @dev     The selector of this function is "dynamic", since it depends on `z_len`.
     */
    function verifyNovaProof(
        // inputs are grouped to prevent errors due stack too deep
        uint256[3] calldata i_z0_zi, // [i, z0, zi] where |z0| == |zi|
        uint256[4] calldata U_i_cmW_U_i_cmE, // [U_i_cmW[2], U_i_cmE[2]]
        uint256[2] calldata u_i_cmW, // [u_i_cmW[2]]
        uint256[3] calldata cmT_r, // [cmT[2], r]
        uint256[2] calldata pA, // groth16 
        uint256[2][2] calldata pB, // groth16
        uint256[2] calldata pC, // groth16
        uint256[4] calldata challenge_W_challenge_E_kzg_evals, // [challenge_W, challenge_E, eval_W, eval_E]
        uint256[2][2] calldata kzg_proof // [proof_W, proof_E]
    ) public view returns (bool) {

        require(i_z0_zi[0] >= 2, "Folding: the number of folded steps should be at least 2");

        // from gamma_abc_len, we subtract 1. 
        uint256[38] memory public_inputs; 

        public_inputs[0] = 12502761034618126622705188176645193720030311898664827637549092351120910133173;
        public_inputs[1] = i_z0_zi[0];

        for (uint i = 0; i < 2; i++) {
            public_inputs[2 + i] = i_z0_zi[1 + i];
        }

        {
            // U_i.cmW + r * u_i.cmW
            uint256[2] memory mulScalarPoint = super.mulScalar([u_i_cmW[0], u_i_cmW[1]], cmT_r[2]);
            uint256[2] memory cmW = super.add([U_i_cmW_U_i_cmE[0], U_i_cmW_U_i_cmE[1]], mulScalarPoint);

            {
                uint256[5] memory cmW_x_limbs = LimbsDecomposition.decompose(cmW[0]);
                uint256[5] memory cmW_y_limbs = LimbsDecomposition.decompose(cmW[1]);
        
                for (uint8 k = 0; k < 5; k++) {
                    public_inputs[4 + k] = cmW_x_limbs[k];
                    public_inputs[9 + k] = cmW_y_limbs[k];
                }
            }
        
            require(this.check(cmW, kzg_proof[0], challenge_W_challenge_E_kzg_evals[0], challenge_W_challenge_E_kzg_evals[2]), "KZG: verifying proof for challenge W failed");
        }

        {
            // U_i.cmE + r * cmT
            uint256[2] memory mulScalarPoint = super.mulScalar([cmT_r[0], cmT_r[1]], cmT_r[2]);
            uint256[2] memory cmE = super.add([U_i_cmW_U_i_cmE[2], U_i_cmW_U_i_cmE[3]], mulScalarPoint);

            {
                uint256[5] memory cmE_x_limbs = LimbsDecomposition.decompose(cmE[0]);
                uint256[5] memory cmE_y_limbs = LimbsDecomposition.decompose(cmE[1]);
            
                for (uint8 k = 0; k < 5; k++) {
                    public_inputs[14 + k] = cmE_x_limbs[k];
                    public_inputs[19 + k] = cmE_y_limbs[k];
                }
            }

            require(this.check(cmE, kzg_proof[1], challenge_W_challenge_E_kzg_evals[1], challenge_W_challenge_E_kzg_evals[3]), "KZG: verifying proof for challenge E failed");
        }

        {
            // add challenges
            public_inputs[24] = challenge_W_challenge_E_kzg_evals[0];
            public_inputs[25] = challenge_W_challenge_E_kzg_evals[1];
            public_inputs[26] = challenge_W_challenge_E_kzg_evals[2];
            public_inputs[27] = challenge_W_challenge_E_kzg_evals[3];

            uint256[5] memory cmT_x_limbs;
            uint256[5] memory cmT_y_limbs;
        
            cmT_x_limbs = LimbsDecomposition.decompose(cmT_r[0]);
            cmT_y_limbs = LimbsDecomposition.decompose(cmT_r[1]);
        
            for (uint8 k = 0; k < 5; k++) {
                public_inputs[24 + 4 + k] = cmT_x_limbs[k]; 
                public_inputs[29 + 4 + k] = cmT_y_limbs[k];
            }

            bool success_g16 = this.verifyProof(pA, pB, pC, public_inputs);
            require(success_g16 == true, "Groth16: verifying proof failed");
        }

        return(true);
    }
}