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

    
    uint256 constant IC0x = 6899681417884702524314678545944021268180904701071892786969696165441874997691;
    uint256 constant IC0y = 3143687136798403451996825981336427812260610111631894268672793896115434574596;
    
    uint256 constant IC1x = 16440825005053599338117416160354828930838648204766930163585884997054470092504;
    uint256 constant IC1y = 3470692732874397613740350236215550107007474703084979629630136261255275344228;
    
    uint256 constant IC2x = 9881175254797142634135442997956080387874716205792162743210523868334546813608;
    uint256 constant IC2y = 6283667233994745780090317334497060485528049293316795898420958952708285641401;
    
    uint256 constant IC3x = 15606875428435837158708880453126129465214663315696951246633813653174576894943;
    uint256 constant IC3y = 2039630823444126828825445375954043672592038140177665212536827477603903611210;
    
    uint256 constant IC4x = 11690743690846007071682140009995842028818757151497267588555946745214296963688;
    uint256 constant IC4y = 12399401121725551214410554126924600889501420502788150398555381057960331987925;
    
    uint256 constant IC5x = 14767983338693591591871263674802184727879403663972494377484289123435253956447;
    uint256 constant IC5y = 17571733982604971484045968466367312087892547710793208596126752905286058331569;
    
    uint256 constant IC6x = 15128548815758649304574143427040721583041910561037696695545105848560056598397;
    uint256 constant IC6y = 3627761224156694363078416670674340999372053962539789415445722442494982100862;
    
    uint256 constant IC7x = 13017087151358612296986464654346136113321127985850865544450080261876642590000;
    uint256 constant IC7y = 11261429560278254100379820452639120077877326292370044615291842879541712220300;
    
    uint256 constant IC8x = 9561767883804056577489741586402333813819203834624886076642767773655011353648;
    uint256 constant IC8y = 18648894380415280881197337335040459149219979392861520832194677168312636720146;
    
    uint256 constant IC9x = 2894326048289615206936485146617445542901405714984920489650181021659119106090;
    uint256 constant IC9y = 21292994612774335981018530582235738347944361364487681273208155145061607553649;
    
    uint256 constant IC10x = 7703070614157751061747921609246160742151139491710794178897159068418819499370;
    uint256 constant IC10y = 4660465501908411629869773093404573750701820892299297884098190156405503787201;
    
    uint256 constant IC11x = 7530800849450868857428519374403434635674820118130614060611856146281759489962;
    uint256 constant IC11y = 10695296696656761208121443517105544120472586287009465220018268500898073208406;
    
    uint256 constant IC12x = 2473145853760779741002287237457419634337799622027336090654909037331375004041;
    uint256 constant IC12y = 5682553105347537895123018494488142760095343067873105805973303822779257248410;
    
    uint256 constant IC13x = 14360676744189579547230555961796626915469915463187740568237317594058260447106;
    uint256 constant IC13y = 13046091963984171125740594324370697795402163762570871992687133913155811500948;
    
    uint256 constant IC14x = 9577636593365700450499395589375776165256305247452508255603065626813209099194;
    uint256 constant IC14y = 19706804527245072304147754432568425592554310947971583972331472209418102388730;
    
    uint256 constant IC15x = 12597983603037972421832327371731951229299960446215460920965691692633473580684;
    uint256 constant IC15y = 9883139500370992913815502596232838161750767596739967537814178675701452296760;
    
    uint256 constant IC16x = 9586395087663821492048625141530153270893128832483041251833937472178457980306;
    uint256 constant IC16y = 18514141178840413474414423058665493719319541497839264526408999485571442386847;
    
    uint256 constant IC17x = 911755366739471893599929277078370540916398267071117035306444046251047858374;
    uint256 constant IC17y = 19597073141560899782564014422363627311790997476071433417115598693080720447657;
    
    uint256 constant IC18x = 14486361945456165791650382926917650597983800105533268187337282829906820901046;
    uint256 constant IC18y = 3095275116370905888179588588562069419142980343636310019451786068227463411216;
    
    uint256 constant IC19x = 12509947044829150716597877498070941367490634676502261830029613057953147564096;
    uint256 constant IC19y = 16948920806391701301576773298135368366132988096945324934125728291822318523786;
    
    uint256 constant IC20x = 8456750290270262854154421007634261501559733289190967372217003542523571543419;
    uint256 constant IC20y = 14321593077519140912720085784313747546533341159711951836840903722065316335754;
    
    uint256 constant IC21x = 1042132870480766661257769429974701655949729958356567526860706176049848205211;
    uint256 constant IC21y = 10237304142989418184399996362213936733385689701438195597559156987728679289997;
    
    uint256 constant IC22x = 13564716433333759014426367123013114755614259412760152927635423357842920616187;
    uint256 constant IC22y = 15857063235248824658846599054564583810948315324774086946490454342169467809174;
    
    uint256 constant IC23x = 12736159573403202297122929908954136243766438151842348095726725317970603870240;
    uint256 constant IC23y = 16670302898423233883067586646612767903622688849374040224202319096337831601960;
    
    uint256 constant IC24x = 15041401646581519883557293318417066551391268739258186811570141191376176633966;
    uint256 constant IC24y = 21257900748282170994687306173522177606054241624984473620478387876997109418561;
    
    uint256 constant IC25x = 21296072278532901252483040386940635227907861314652921645772238034848062563621;
    uint256 constant IC25y = 19456184561476022917642624352138786326224858169824011645815262964847986717978;
    
    uint256 constant IC26x = 13594619598419900820545588665447830710080824532987976612885600333040664941805;
    uint256 constant IC26y = 15652721420411366098773841562859427777381232059671699889864488074168332652495;
    
    uint256 constant IC27x = 17190934304394351781723498238382684690599304203007365179791589106992130312656;
    uint256 constant IC27y = 9811733356453613763373089078316723276099268893459370035083929727644054172970;
    
    uint256 constant IC28x = 18121001262292235695297154155136436989139058683752293107375876493286701887192;
    uint256 constant IC28y = 19190207914420358927991509874284258712804086454401655740795371522381961149493;
    
    uint256 constant IC29x = 12397844697521812933882859027212924044680946430904977754785624733505501714896;
    uint256 constant IC29y = 7369935918746574066325589268501671983949983239223252147181129942720560776186;
    
    uint256 constant IC30x = 8289166504147003108478812344242387165636908467382811821846265385531568766979;
    uint256 constant IC30y = 2538482768764423547405558102594277411330409714196680194622681862780256905328;
    
    uint256 constant IC31x = 7561405583076097380751372468116053269300306085964509354231897147167416373709;
    uint256 constant IC31y = 15085672907262764210280007384398972693941737814366190210260966988709871251158;
    
    uint256 constant IC32x = 7285034089648907501362896411764127578828423534249665054208981569260962814448;
    uint256 constant IC32y = 11280274536795038405600541901628426268653626954482247053592389507658630041083;
    
    uint256 constant IC33x = 14173295182699449493359274226315365390197163907388024376054112949838606601797;
    uint256 constant IC33y = 20531180779400619312444936048215410209643992896881857963552654441938526730482;
    
    uint256 constant IC34x = 21429876010867160978202107469442703900983409053500713335904305337058852058579;
    uint256 constant IC34y = 20922840463682705949141069141953144307396825113931046155060721078979320976162;
    
    uint256 constant IC35x = 932288102131424646541738663706325539165438446500481691249988074377527613616;
    uint256 constant IC35y = 19324717952737639616916379920940679094334567734544622583224115146961236813612;
    
    uint256 constant IC36x = 18030034457994639411355335910208413640807321375174260346114443456515886778794;
    uint256 constant IC36y = 5961148606089323625238746508968591197395347816575002143344983504022404066188;
    
    uint256 constant IC37x = 19108010623444410477046619482182341088246442917407887729108703049575731067908;
    uint256 constant IC37y = 5330830095018102172827246054776945727339154179950606943720548710893628490035;
    
    uint256 constant IC38x = 6902160587909855181458646514414419282602036815944916384823252131318512003542;
    uint256 constant IC38y = 391168998854097492558474575503433511405309606678525056523428624370033150938;
    
    uint256 constant IC39x = 1184744673834746509065508570368697831341603700310947414282328269059658776520;
    uint256 constant IC39y = 9255299097404018304414809437180256845543181248492620317455880781794952528326;
    
    uint256 constant IC40x = 21242103566706543732840645683685558536618961998649531960353405720120524823605;
    uint256 constant IC40y = 10274998870882113507289674844152325539564447633189329225510772287642970850342;
    
    
    // Memory data
    uint16 constant pVk = 0;
    uint16 constant pPairing = 128;

    uint16 constant pLastMem = 896;

    function verifyProof(uint[2] calldata _pA, uint[2][2] calldata _pB, uint[2] calldata _pC, uint[40] calldata _pubSignals) public view returns (bool) {
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
        uint256[2] calldata initial_state, // initial IVC state (z0)
        uint256[2] calldata final_state, // IVC state after i steps (zi)
        uint256[25] calldata proof // the rest of the decider inputs
    ) external view returns (bool);

    /**
     * @notice  Verifies a Nova+CycleFold proof given all the proof inputs collected in a single array.
     * @dev     This function should simply reorganize arguments and pass them to the proper verification function.
     */
    function verifyOpaqueNovaProof(uint256[30] calldata proof) external view returns (bool);
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
        uint256[5] calldata i_z0_zi, // [i, z0, zi] where |z0| == |zi|
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
        uint256[40] memory public_inputs; 

        public_inputs[0] = 16929260548350046279927038787425857929397563146398131636474636286728193065143;
        public_inputs[1] = i_z0_zi[0];

        for (uint i = 0; i < 4; i++) {
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
                    public_inputs[6 + k] = cmW_x_limbs[k];
                    public_inputs[11 + k] = cmW_y_limbs[k];
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
                    public_inputs[16 + k] = cmE_x_limbs[k];
                    public_inputs[21 + k] = cmE_y_limbs[k];
                }
            }

            require(this.check(cmE, kzg_proof[1], challenge_W_challenge_E_kzg_evals[1], challenge_W_challenge_E_kzg_evals[3]), "KZG: verifying proof for challenge E failed");
        }

        {
            // add challenges
            public_inputs[26] = challenge_W_challenge_E_kzg_evals[0];
            public_inputs[27] = challenge_W_challenge_E_kzg_evals[1];
            public_inputs[28] = challenge_W_challenge_E_kzg_evals[2];
            public_inputs[29] = challenge_W_challenge_E_kzg_evals[3];

            uint256[5] memory cmT_x_limbs;
            uint256[5] memory cmT_y_limbs;
        
            cmT_x_limbs = LimbsDecomposition.decompose(cmT_r[0]);
            cmT_y_limbs = LimbsDecomposition.decompose(cmT_r[1]);
        
            for (uint8 k = 0; k < 5; k++) {
                public_inputs[26 + 4 + k] = cmT_x_limbs[k]; 
                public_inputs[31 + 4 + k] = cmT_y_limbs[k];
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
        uint256[2] calldata initial_state,
        uint256[2] calldata final_state,
        uint256[25] calldata proof
    ) public override view returns (bool) {
        uint256[1 + 2 * 2] memory i_z0_zi;
        i_z0_zi[0] = steps;
        for (uint256 i = 0; i < 2; i++) {
            i_z0_zi[i + 1] = initial_state[i];
            i_z0_zi[i + 1 + 2] = final_state[i];
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
    function verifyOpaqueNovaProof(uint256[30] calldata proof) public override view returns (bool) {
        uint256[2] memory z0;
        uint256[2] memory zi;
        for (uint256 i = 0; i < 2; i++) {
            z0[i] = proof[i + 1];
            zi[i] = proof[i + 1 + 2];
        }

        uint256[25] memory extracted_proof;
        for (uint256 i = 0; i < 25; i++) {
            extracted_proof[i] = proof[5 + i];
        }

        return this.verifyOpaqueNovaProofWithInputs(proof[0], z0, zi, extracted_proof);
    }
}