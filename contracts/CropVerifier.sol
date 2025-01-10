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

    
    uint256 constant IC0x = 21722744695151930251507193407151702334749725170407822325530049154587521688271;
    uint256 constant IC0y = 14147862530531576245293342630261660921387597982522650185365351891681932577025;
    
    uint256 constant IC1x = 963259269670861429673156213599475272093082661824815612433542470063962716186;
    uint256 constant IC1y = 7245190941240955358287574036473184101062008960186924269392831442774641471423;
    
    uint256 constant IC2x = 11591408041618018499944422777830049556780949574297862601243410098150367829051;
    uint256 constant IC2y = 9934484061936824691606010215467729746229800328259805919492890888454477125119;
    
    uint256 constant IC3x = 19156277608049904179629936323054268003073717404943568052982695653158392169425;
    uint256 constant IC3y = 13884678715270039296033911910571439777552433084292834149320042255205544938381;
    
    uint256 constant IC4x = 3117154002992364821244325014197421744553869403644434280399279039760243416841;
    uint256 constant IC4y = 10518303823669305011317136637148603680296078480055116526817288139175329911732;
    
    uint256 constant IC5x = 19923578653739220947928364222497017639265377306073688938950145839633132500618;
    uint256 constant IC5y = 1250844184531820160346600650481654692476923630614193289313499413660007809662;
    
    uint256 constant IC6x = 13879620119331147641878980077128818904901722373727496398944658030775149439419;
    uint256 constant IC6y = 7158486923697631461300059859087658282323472753467297276241404345537982181554;
    
    uint256 constant IC7x = 16404754158771647295317180624629857606796732267764334136586557147588501120047;
    uint256 constant IC7y = 10271251845518485481723756198330293317149886769323816854458574442602782965032;
    
    uint256 constant IC8x = 3776941945025382969936961820070070948419867323886950891670583008099477710457;
    uint256 constant IC8y = 15293853720310441215366098089098193096139410908437158292543506196295877751056;
    
    uint256 constant IC9x = 6329479084560436093953022667080449478788394548141626740612986643788505937630;
    uint256 constant IC9y = 17382420324736889884976797921296721357812933822182911639006154500688734249729;
    
    uint256 constant IC10x = 12220873123769076586838247370271632979523606926474841500334887832980059296231;
    uint256 constant IC10y = 3343397350749116038822070830088585466593318780574285775748633975854119218407;
    
    uint256 constant IC11x = 1718791627758275134831592422096120709030617496674755955184478492531495842652;
    uint256 constant IC11y = 5012795448340881199761470039497801541423178465035305161530275221867023813940;
    
    uint256 constant IC12x = 2020531759957361166845541826885119547488984186510891957814799176622334609670;
    uint256 constant IC12y = 195275849197062628881108258314442191258928795942180148930936581053081216914;
    
    uint256 constant IC13x = 13166680897432896820768738562050806504688727245301953269105593916574184575544;
    uint256 constant IC13y = 8703272197094698228332428978757536120120412732971434991660420518780758499616;
    
    uint256 constant IC14x = 7236430822426136548009600040519542071895389450459812064533443908949693342565;
    uint256 constant IC14y = 12504663627502928487096966030464593535432479605996685378029017697797115598759;
    
    uint256 constant IC15x = 6040015743559417785498560131780836189932530723755332533276597858072893884683;
    uint256 constant IC15y = 16287408938409912382887406057971341652891827785577155380177799442434462495295;
    
    uint256 constant IC16x = 18205137574605805679698252698600293227708875621726806765052679736352733483367;
    uint256 constant IC16y = 11675516684120456806756907831698274054315131472200135469878790033811771896109;
    
    uint256 constant IC17x = 6720040774495486890658747323218523537950797650399503132323186412768496178521;
    uint256 constant IC17y = 20083607698781966028050144653075852961239320211968415991954072431457917089487;
    
    uint256 constant IC18x = 20842499161293285471596343329675691001084879826581817568225189224519341585193;
    uint256 constant IC18y = 7942899520419611731938163498739877502633111604754422737127224869574358234719;
    
    uint256 constant IC19x = 21106003728979432606982656884783083908108136389121038145619060547979124137969;
    uint256 constant IC19y = 2462955835977710197967981546680392270545554371567955187857333879242382617161;
    
    uint256 constant IC20x = 17448132887678189167078840305759652319435243305869845647669034414529543007906;
    uint256 constant IC20y = 18011490785724404737587301657271439022235679767698761048243149681880321694326;
    
    uint256 constant IC21x = 6924757448067397167348199945070928807435659432305692751762252690356105639957;
    uint256 constant IC21y = 9767369540890120945885842655792739286639653031073390155970711861199222305191;
    
    uint256 constant IC22x = 13499317521639218411302716505278287874486782663260562506610004605224709439444;
    uint256 constant IC22y = 210113797396119413285205886708796313305727737735085061485281052634188570287;
    
    uint256 constant IC23x = 214346869652087818686027701866499626541312652825708923307377027536717489771;
    uint256 constant IC23y = 13051017062875625895436283802453048726667956418172429731269228518669202534115;
    
    uint256 constant IC24x = 5299609383514627500668069762274652240425967484261661463752786799016101892415;
    uint256 constant IC24y = 359074291234896967975763709042769123338780103347979503585908642422531340196;
    
    uint256 constant IC25x = 6178212853786122428780773881111177645971556640980808544704997297819067679982;
    uint256 constant IC25y = 14822958556305606846910295911825729534161903351672519625699608735378122789120;
    
    uint256 constant IC26x = 15898026020575883970876673705089380696095826605984059850950103226418214154356;
    uint256 constant IC26y = 19073177221079532118547777644687524466135443263917132719072557858598074007188;
    
    uint256 constant IC27x = 19615325675023302415793631262706155339500062545293405575720483773486896056914;
    uint256 constant IC27y = 5567678900869738670219798548926470338465625912877916154704384820923532921399;
    
    uint256 constant IC28x = 13625472643271823951040357442882002363567270578201848640022293798751673136856;
    uint256 constant IC28y = 106409594781707605616259522751945343901076705661860493158514272866324194306;
    
    uint256 constant IC29x = 9132995919841812558737100319589444182290330050679422968389592911285745899379;
    uint256 constant IC29y = 9789527495246932175422999929076471474797912127189783803920818659239857112463;
    
    uint256 constant IC30x = 7505487079340618132680490684187758393916524655728162661260202509890254276040;
    uint256 constant IC30y = 11205069063864854844979133787908454687847849584955491956215774947735656421744;
    
    uint256 constant IC31x = 1051225224002044275037981295463384833786376976125495432643142146336351378270;
    uint256 constant IC31y = 12782428120781453023172084907024085572781100565741128681938855718917008691942;
    
    uint256 constant IC32x = 18733002808368616518770506404489452122595687114836305915723373757996931118315;
    uint256 constant IC32y = 6736200244218851639538207286287396459252035279638607206225675149980462310635;
    
    uint256 constant IC33x = 7358238334169602766263887782798249420038271471775689596644822431312348946627;
    uint256 constant IC33y = 14682774372276930902595295685326090950941504765768215548872562488345858101621;
    
    uint256 constant IC34x = 11264447343267245864896722951633078600727927688891579740626901738856215036405;
    uint256 constant IC34y = 295500617087095464859785060421173944231107166903363683926062438025149132647;
    
    uint256 constant IC35x = 16017227854860410708922711059244691574247784409283010900726012244122717315512;
    uint256 constant IC35y = 14429710496791077439020703123686262012623731688454126083537365394507066175088;
    
    uint256 constant IC36x = 14907997089520463674510344563766675109239324695023732213761829117856279289516;
    uint256 constant IC36y = 8601809011665271861407026600999743150398485890279369267827964622866611882409;
    
    uint256 constant IC37x = 11998787384294370161092963151746145254349913681805668149482821676229965007870;
    uint256 constant IC37y = 14905799292482827232081792853226740898480882566923091670033239873950201390076;
    
    uint256 constant IC38x = 12997979182197652681982345348036743069546858284879413497911876759973134323816;
    uint256 constant IC38y = 12084972699117711845750079571073053687854439439474494719363363557652228118863;
    
    uint256 constant IC39x = 9777724081124397020732768306025993820040095697184769047570426685043088620995;
    uint256 constant IC39y = 17248864203521924864477720596234844608750067742334645478456805455591787110640;
    
    uint256 constant IC40x = 17517889648909064192061219126746747076785464821518998741788323357412270156809;
    uint256 constant IC40y = 4917598381072676106108274153230738835516166991728617930891018811124631459471;
    
    uint256 constant IC41x = 2825496482325981496038768493074325202924149738826910331993498472914479484920;
    uint256 constant IC41y = 2452293141065690534985728039713182325657382517123610476767571180415345929687;
    
    uint256 constant IC42x = 17849065975109979700374973033875741027712316374845914925820208563025751531978;
    uint256 constant IC42y = 11299389347260898661620078632965215140724340454600534769771206518868450063164;
    
    
    // Memory data
    uint16 constant pVk = 0;
    uint16 constant pPairing = 128;

    uint16 constant pLastMem = 896;

    function verifyProof(uint[2] calldata _pA, uint[2][2] calldata _pB, uint[2] calldata _pC, uint[42] calldata _pubSignals) public view returns (bool) {
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
        uint256[7] calldata i_z0_zi, // [i, z0, zi] where |z0| == |zi|
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
        uint256[42] memory public_inputs; 

        public_inputs[0] = 156389281254492112637625220580162124755717475898883961894420409869875251993;
        public_inputs[1] = i_z0_zi[0];

        for (uint i = 0; i < 6; i++) {
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
                    public_inputs[8 + k] = cmW_x_limbs[k];
                    public_inputs[13 + k] = cmW_y_limbs[k];
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
                    public_inputs[18 + k] = cmE_x_limbs[k];
                    public_inputs[23 + k] = cmE_y_limbs[k];
                }
            }

            require(this.check(cmE, kzg_proof[1], challenge_W_challenge_E_kzg_evals[1], challenge_W_challenge_E_kzg_evals[3]), "KZG: verifying proof for challenge E failed");
        }

        {
            // add challenges
            public_inputs[28] = challenge_W_challenge_E_kzg_evals[0];
            public_inputs[29] = challenge_W_challenge_E_kzg_evals[1];
            public_inputs[30] = challenge_W_challenge_E_kzg_evals[2];
            public_inputs[31] = challenge_W_challenge_E_kzg_evals[3];

            uint256[5] memory cmT_x_limbs;
            uint256[5] memory cmT_y_limbs;
        
            cmT_x_limbs = LimbsDecomposition.decompose(cmT_r[0]);
            cmT_y_limbs = LimbsDecomposition.decompose(cmT_r[1]);
        
            for (uint8 k = 0; k < 5; k++) {
                public_inputs[28 + 4 + k] = cmT_x_limbs[k]; 
                public_inputs[33 + 4 + k] = cmT_y_limbs[k];
            }

            bool success_g16 = this.verifyProof(pA, pB, pC, public_inputs);
            require(success_g16 == true, "Groth16: verifying proof failed");
        }

        return(true);
    }
}