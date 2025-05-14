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

    
    uint256 constant IC0x = 1387714227744558787113951074452021948115937171617158753125192604795629095583;
    uint256 constant IC0y = 19088010886313577388475725152025251851494768412440603632829379923566757390163;
    
    uint256 constant IC1x = 3993396608968986358052772154905809887205187572562753054714923915975376972866;
    uint256 constant IC1y = 11034916269862993322229633522618735045131788212984377698249434894005091860116;
    
    uint256 constant IC2x = 13152919954956749843590443558378395740318337769532886707878855039038512604490;
    uint256 constant IC2y = 6638482040778458216629443457070850528156795020688935472664751353416412943046;
    
    uint256 constant IC3x = 1776435574193441380338862626619557115569640347043278237943809271099372561438;
    uint256 constant IC3y = 18139701430282196864422659257314692247040083088890679537987028995401506678939;
    
    uint256 constant IC4x = 17232266993018726479229927794949930254963921284033490466737835333691770675973;
    uint256 constant IC4y = 1077674531316263060407251717877994618244402018062770468071732670760651507523;
    
    uint256 constant IC5x = 5394488372121373174624782708666577540862035901741974129116511497416325792753;
    uint256 constant IC5y = 20438594299183391194421918150778883978196705202358579610545238585861216910539;
    
    uint256 constant IC6x = 1683148366701503870243603789427216161336204044119205495857528283868196602259;
    uint256 constant IC6y = 11968459132929605406205526154285274239270932158101742673479531810054927218320;
    
    uint256 constant IC7x = 15951999237386734503779824078730302491016070794813180415993562890195916353992;
    uint256 constant IC7y = 12474935657366134731251705393193525969799379815207793793177395097611226872727;
    
    uint256 constant IC8x = 6352539134588875600603364168816634386386382541026199185841191056350416734188;
    uint256 constant IC8y = 16184181224537597669820707307825710339928690370241927314308717840282135936145;
    
    uint256 constant IC9x = 20244852080031147377179602029727858224106414509707670944967764905270430435739;
    uint256 constant IC9y = 17708158590648698237083464361994983325422833880714481177472685408118801380633;
    
    uint256 constant IC10x = 16959505132563213861251106622032332640290857990151096918102171632567196413055;
    uint256 constant IC10y = 2054607356518910845938246472627726534754391800276295047693320991041589539780;
    
    uint256 constant IC11x = 6285796552835589338426356677026842201514081082734375690339448126756026249783;
    uint256 constant IC11y = 6669195516198416212501550915224770792613359119384668446202112898217636193914;
    
    uint256 constant IC12x = 2721556911897870582365217330421602625103441473099998529249099778456138912985;
    uint256 constant IC12y = 6386243436656203456280521644411363117993968203875080809521606080612718778635;
    
    uint256 constant IC13x = 9118209865470621343969553242554304128251042657944194194811820211772925801598;
    uint256 constant IC13y = 4023676600106094312427776581353075154208003725970879032886713447162894144839;
    
    uint256 constant IC14x = 8146906136053039049125959475513359231851727698531946179681689604880023205401;
    uint256 constant IC14y = 20336316245793235109336515883733874445555827492702881623084755016249854482803;
    
    uint256 constant IC15x = 10744893357562263046758688711138355071278106574660871619804625427900383199925;
    uint256 constant IC15y = 9589602545963140716915211429401485241490694128599791329450648846821234537388;
    
    uint256 constant IC16x = 9047293417725623044829657827941492989247402187492003681152129913660183915711;
    uint256 constant IC16y = 12155189894637181639625264630198109994911448788759374745204711253811746237984;
    
    uint256 constant IC17x = 3033665849080939630952517263893778410012397280479696188800158747902765266694;
    uint256 constant IC17y = 6024003779167513424141464999693774717838125475604163827938896202954889631913;
    
    uint256 constant IC18x = 9113875068456332634367113980317787788288124818693853572404466785576729021710;
    uint256 constant IC18y = 14551197831255682226184209452114391098236149965782230970722488318006849380183;
    
    uint256 constant IC19x = 7666548407804745038757318865822957549687116068387430045430286812517705560070;
    uint256 constant IC19y = 6527537822186638841759227419352115215762501471918750075501336137479449348309;
    
    uint256 constant IC20x = 14878832435754694238217292119346437175019575306741720639335139843332156764204;
    uint256 constant IC20y = 2039587727270156688754364594364302648163789270652664598043744466045929824643;
    
    uint256 constant IC21x = 6122487561718325759816276031077193690289942015055251819786387044112698435107;
    uint256 constant IC21y = 787724256756312007378701486802926736842509710997130872207445427349135518716;
    
    uint256 constant IC22x = 8843587525243883875606952209918184711374067677002078250299512120283209551679;
    uint256 constant IC22y = 4333968213502079381097052581937864271225403806493712895114186533639886411327;
    
    uint256 constant IC23x = 4247302597268108270161806123001252112740601244440125275321868093910145699402;
    uint256 constant IC23y = 7742550739233684920584384520400728644652375278930548259151335210797577205545;
    
    uint256 constant IC24x = 8683523283163650015686806377383359034110542804293252453898884298121706922356;
    uint256 constant IC24y = 11900600825791565288299275754166179952702140817118683508230823286663867582005;
    
    uint256 constant IC25x = 18238605824410797323311293858808772309455836122243042435834176115660177541549;
    uint256 constant IC25y = 862897475526605321874743918039502015560894437511227538336556219469923853602;
    
    uint256 constant IC26x = 10835086911240949508234325354455102916791404689268153922971507161475515848275;
    uint256 constant IC26y = 4568047179471035850259399552127528454188655870625984485781836885432943982893;
    
    uint256 constant IC27x = 8693295344219041963135161386461561604945209379281736905524816771682584177336;
    uint256 constant IC27y = 15483840261979272205407800199907489778884873566942277550944564562810663201078;
    
    uint256 constant IC28x = 4279130958175250322201966986300336296597804677638365939216430680509771150686;
    uint256 constant IC28y = 11916957277958849229521253762237016476147987786029748406140116121048364454888;
    
    uint256 constant IC29x = 10153980765759850419043348827827019221545486670243264278566479753543403682183;
    uint256 constant IC29y = 12236529827046178868123189357791301063510802744300009111434809268259469819632;
    
    uint256 constant IC30x = 8951717600424008366740825108996364997369946452342989327479332772422025338528;
    uint256 constant IC30y = 3342632302958367198155951988243995574061309127781360056109929393071657266951;
    
    uint256 constant IC31x = 20053004137254239888948231505128726261736497745118962092545050480145536473013;
    uint256 constant IC31y = 14812156863690927576121390992031039707039512878965440541795665705003443881152;
    
    uint256 constant IC32x = 9442364493610492916295434370937285470280768563396837493971680230564781920473;
    uint256 constant IC32y = 669123804718917249961001863060440487277076363990356646261277402165648878498;
    
    uint256 constant IC33x = 20431347790506114975022962535605006393995956498531318389976039080383770018557;
    uint256 constant IC33y = 2576260126827856727744953054370617696973035670436460339906298295093252700257;
    
    uint256 constant IC34x = 9402444394476157619096631531206282468104641291366878068048458165529275139978;
    uint256 constant IC34y = 14112339101510890542147311845310720791940816635057374748554103977275350102479;
    
    uint256 constant IC35x = 15899042401559979273155343592897879601794100358613560098066013708642649916998;
    uint256 constant IC35y = 3989654852385305517475537676569970062531381352048329262326764656896468884367;
    
    uint256 constant IC36x = 20431122979457040657580798030446577948139437600536352153200852873744375486042;
    uint256 constant IC36y = 14035050077099495161629513752321397606715132310573516440107682591947867576089;
    
    uint256 constant IC37x = 13544948568294374286599417886473144239269809714468669395877783916007709068239;
    uint256 constant IC37y = 15047818770527163933590504875212700406644929215300181257454139390781638705217;
    
    uint256 constant IC38x = 17239151206352207007570893189731765664806473283081857896755959516673153154366;
    uint256 constant IC38y = 10835836091516420835101450583109491193249494791603562968566007251043422834703;
    
    uint256 constant IC39x = 11473329989024870948059175144158235402759672953202428961402114384794779560606;
    uint256 constant IC39y = 12192019581387114580751607858310646823145602189822661487034068628915593513915;
    
    uint256 constant IC40x = 12711562704839408918459038819402450040048886244123219508617612766489305411349;
    uint256 constant IC40y = 629640157551426210599625749979935895205598988812076785462919364292207828780;
    
    uint256 constant IC41x = 59074194124497409152009801202909214449836942356176685672759186188644089002;
    uint256 constant IC41y = 9611991434604675981307293955803385747249856214231576683770060180228889125414;
    
    uint256 constant IC42x = 7995440478898413353936842582270202993206521798371402034208709835803742687854;
    uint256 constant IC42y = 18018831963443360604975407233645639207283384989047930118075042117323684599021;
    
    uint256 constant IC43x = 21230427951306733413421813897437680823956042295027876097797168476386306471497;
    uint256 constant IC43y = 16900353639149087807744402038969939284459637644480406970408793607673258853279;
    
    uint256 constant IC44x = 18151548822356177418631243850551472766504594855191511090438384390259241375472;
    uint256 constant IC44y = 9592813843639967984243168085450578337650632006763963421284863322700886726049;
    
    
    // Memory data
    uint16 constant pVk = 0;
    uint16 constant pPairing = 128;

    uint16 constant pLastMem = 896;

    function verifyProof(uint[2] calldata _pA, uint[2][2] calldata _pB, uint[2] calldata _pC, uint[44] calldata _pubSignals) public view returns (bool) {
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
                g1_mulAccC(_pVk, IC39x, IC39y, calldataload(add(pubSignals, 1216)))
                g1_mulAccC(_pVk, IC40x, IC40y, calldataload(add(pubSignals, 1248)))
                g1_mulAccC(_pVk, IC41x, IC41y, calldataload(add(pubSignals, 1280)))
                g1_mulAccC(_pVk, IC42x, IC42y, calldataload(add(pubSignals, 1312)))
                g1_mulAccC(_pVk, IC43x, IC43y, calldataload(add(pubSignals, 1344)))
                g1_mulAccC(_pVk, IC44x, IC44y, calldataload(add(pubSignals, 1376)))

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
            
            checkField(calldataload(add(_pubSignals, 1248)))
            
            checkField(calldataload(add(_pubSignals, 1280)))
            
            checkField(calldataload(add(_pubSignals, 1312)))
            
            checkField(calldataload(add(_pubSignals, 1344)))
            
            checkField(calldataload(add(_pubSignals, 1376)))
            
            checkField(calldataload(add(_pubSignals, 1408)))
            

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
 * @author PSE & 0xPARC
 * @title  Interface for the NovaDecider contract hiding proof details.
 * @dev    This interface enables calling the verifyNovaProof function without exposing the proof details.
 */
interface OpaqueDecider {
    /**
     * @notice  Verifies a Nova+CycleFold proof given initial and final IVC states, number of steps and the rest proof inputs concatenated.
     * @dev     This function should simply reorganize arguments and pass them to the proper verification function.
     */
    function verifyOpaqueNovaProofWithInputs(
        uint256 steps, // number of folded steps (i)
        uint256[4] calldata initial_state, // initial IVC state (z0)
        uint256[4] calldata final_state, // IVC state after i steps (zi)
        uint256[25] calldata proof // the rest of the decider inputs
    ) external view returns (bool);

    /**
     * @notice  Verifies a Nova+CycleFold proof given all the proof inputs collected in a single array.
     * @dev     This function should simply reorganize arguments and pass them to the proper verification function.
     */
    function verifyOpaqueNovaProof(uint256[34] calldata proof) external view returns (bool);
}

/**
 * @author  PSE & 0xPARC
 * @title   NovaDecider contract, for verifying Nova IVC SNARK proofs.
 * @dev     This is an askama template which, when templated, features a Groth16 and KZG10 verifiers from which this contract inherits.
 */
contract NovaDecider is Groth16Verifier, KZG10Verifier, OpaqueDecider {
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
        uint256[9] calldata i_z0_zi, // [i, z0, zi] where |z0| == |zi|
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
        uint256[44] memory public_inputs; 

        public_inputs[0] = 4726713633347330335916161880384544684437596324529590093502665821935567993646;
        public_inputs[1] = i_z0_zi[0];

        for (uint i = 0; i < 8; i++) {
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
                    public_inputs[10 + k] = cmW_x_limbs[k];
                    public_inputs[15 + k] = cmW_y_limbs[k];
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
                    public_inputs[20 + k] = cmE_x_limbs[k];
                    public_inputs[25 + k] = cmE_y_limbs[k];
                }
            }

            require(this.check(cmE, kzg_proof[1], challenge_W_challenge_E_kzg_evals[1], challenge_W_challenge_E_kzg_evals[3]), "KZG: verifying proof for challenge E failed");
        }

        {
            // add challenges
            public_inputs[30] = challenge_W_challenge_E_kzg_evals[0];
            public_inputs[31] = challenge_W_challenge_E_kzg_evals[1];
            public_inputs[32] = challenge_W_challenge_E_kzg_evals[2];
            public_inputs[33] = challenge_W_challenge_E_kzg_evals[3];

            uint256[5] memory cmT_x_limbs;
            uint256[5] memory cmT_y_limbs;
        
            cmT_x_limbs = LimbsDecomposition.decompose(cmT_r[0]);
            cmT_y_limbs = LimbsDecomposition.decompose(cmT_r[1]);
        
            for (uint8 k = 0; k < 5; k++) {
                public_inputs[30 + 4 + k] = cmT_x_limbs[k]; 
                public_inputs[35 + 4 + k] = cmT_y_limbs[k];
            }

            bool success_g16 = this.verifyProof(pA, pB, pC, public_inputs);
            require(success_g16 == true, "Groth16: verifying proof failed");
        }

        return(true);
    }

    /**
     * @notice  Verifies a Nova+CycleFold proof given initial and final IVC states, number of steps and the rest proof inputs concatenated.
     * @dev     Simply reorganization of arguments and call to the `verifyNovaProof` function.
     */
    function verifyOpaqueNovaProofWithInputs(
        uint256 steps,
        uint256[4] calldata initial_state,
        uint256[4] calldata final_state,
        uint256[25] calldata proof
    ) public override view returns (bool) {
        uint256[1 + 2 * 4] memory i_z0_zi;
        i_z0_zi[0] = steps;
        for (uint256 i = 0; i < 4; i++) {
            i_z0_zi[i + 1] = initial_state[i];
            i_z0_zi[i + 1 + 4] = final_state[i];
        }

        uint256[4] memory U_i_cmW_U_i_cmE = [proof[0], proof[1], proof[2], proof[3]];
        uint256[2] memory u_i_cmW = [proof[4], proof[5]];
        uint256[3] memory cmT_r = [proof[6], proof[7], proof[8]];
        uint256[2] memory pA = [proof[9], proof[10]];
        uint256[2][2] memory pB = [[proof[11], proof[12]], [proof[13], proof[14]]];
        uint256[2] memory pC = [proof[15], proof[16]];
        uint256[4] memory challenge_W_challenge_E_kzg_evals = [proof[17], proof[18], proof[19], proof[20]];
        uint256[2][2] memory kzg_proof = [[proof[21], proof[22]], [proof[23], proof[24]]];

        return this.verifyNovaProof(
            i_z0_zi,
            U_i_cmW_U_i_cmE,
            u_i_cmW,
            cmT_r,
            pA,
            pB,
            pC,
            challenge_W_challenge_E_kzg_evals,
            kzg_proof
        );
    }

    /**
     * @notice  Verifies a Nova+CycleFold proof given all proof inputs concatenated.
     * @dev     Simply reorganization of arguments and call to the `verifyNovaProof` function.
     */
    function verifyOpaqueNovaProof(uint256[34] calldata proof) public override view returns (bool) {
        uint256[4] memory z0;
        uint256[4] memory zi;
        for (uint256 i = 0; i < 4; i++) {
            z0[i] = proof[i + 1];
            zi[i] = proof[i + 1 + 4];
        }

        uint256[25] memory extracted_proof;
        for (uint256 i = 0; i < 25; i++) {
            extracted_proof[i] = proof[9 + i];
        }

        return this.verifyOpaqueNovaProofWithInputs(proof[0], z0, zi, extracted_proof);
    }
}