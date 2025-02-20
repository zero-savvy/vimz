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

    
    uint256 constant IC0x = 17092934075687396817661824306743330637947284998916415679070319406444260789612;
    uint256 constant IC0y = 13861404166042924384477737313681230996373176000008842059221885219729529307477;
    
    uint256 constant IC1x = 20475508594340542054630117846972465636339595040619229566095897015238757274469;
    uint256 constant IC1y = 4479664638280216675790892006405866690583598697156520360264015042998735362209;
    
    uint256 constant IC2x = 17981633710156435560711499507537105018357739749150600449960222855957714163503;
    uint256 constant IC2y = 15721837254652323070472152100784359507822258190158334080548187633709690520816;
    
    uint256 constant IC3x = 4366095256597864624717794788576331372310089125818757237323878575786517780624;
    uint256 constant IC3y = 6153138787801366489960301476529480116974894071504339056665081312946476112661;
    
    uint256 constant IC4x = 19379819436202266226197629406987035476595575646114136670809817733643531756536;
    uint256 constant IC4y = 21301762477225323737238944628400073772148646268068640605986903327167778877214;
    
    uint256 constant IC5x = 13997213232272487097571686972890682486712252691369522210986401867520205046371;
    uint256 constant IC5y = 14347960542011202676749617653819796350016357098550552335922021634136011255027;
    
    uint256 constant IC6x = 3273826566378021289797484019079777004822189331393037535626052439179714618329;
    uint256 constant IC6y = 16946982543877262498515595936955504985894174123251860168369829611229807679909;
    
    uint256 constant IC7x = 20760958384006659041334255912891776733982399778597210471619763190311300868631;
    uint256 constant IC7y = 9070880255461837528934973469781673447781252670201730175699908602000815149666;
    
    uint256 constant IC8x = 19654144276723224179942322883837794853807500536868213216563491802627887022889;
    uint256 constant IC8y = 13557289900738761720708321560806976486686456134733909268536296227610405245279;
    
    uint256 constant IC9x = 11202656631200496180507200496929055285402758932318445123498964682615118394359;
    uint256 constant IC9y = 14491080775476592601631848664984495675490853011646366512381145186822203920432;
    
    uint256 constant IC10x = 7689060796930854419382047149248505232540806197239393351831164177111791596207;
    uint256 constant IC10y = 19554742771356253615775858935138967156378524139501145906107876870730837417224;
    
    uint256 constant IC11x = 21518641879640196259204803086914165285343240101397990766244090894786044698416;
    uint256 constant IC11y = 6174643774673920102254620454560671709953870063501899407652459201112384141635;
    
    uint256 constant IC12x = 16212083094109810203118956839878193460493502793185795292420823184383347181053;
    uint256 constant IC12y = 19196450855509842422692032723717153989998920366922280375525704799192013527638;
    
    uint256 constant IC13x = 11706933027350506273292080053035068803701389260474378809978826056199534226467;
    uint256 constant IC13y = 7001900981910975102130080001717410814120168737468269011822214975501350069104;
    
    uint256 constant IC14x = 7909626211118376252498079576435832312167730383292524414897245255312208394641;
    uint256 constant IC14y = 10609457512834267261770066898789286166797113549693310673306162212245030175137;
    
    uint256 constant IC15x = 11885583220440582572267900609982274906403245754735797933592029558157373083622;
    uint256 constant IC15y = 469264853870030856074496685053655870037037488020850856212905765549578267904;
    
    uint256 constant IC16x = 19499111826631082857362190970751014203058424784360595380622268914309402473032;
    uint256 constant IC16y = 9775242998581263366191407745347517572812679534904424860705933313510360131364;
    
    uint256 constant IC17x = 6421022492516109628508156550567194097446542667301976643007296586666088674309;
    uint256 constant IC17y = 9887362582167048806256022533738302081820032580984678287758562289710382185602;
    
    uint256 constant IC18x = 21723054620917817951689687906092113450526874947163772923173942260408863941239;
    uint256 constant IC18y = 6122462719345810372145586255662474397058955030699944244722608204294374431656;
    
    uint256 constant IC19x = 15008510769422852888423246861214521397968356060140893304951570137140430739787;
    uint256 constant IC19y = 16650747112102309929355777815660655921552572094737683108037392938521536631210;
    
    uint256 constant IC20x = 7865659385610404178047767898786332955007171799568437102263348890222072283464;
    uint256 constant IC20y = 15562164356201705653575782961264170232912220247804576377241729782623510745380;
    
    uint256 constant IC21x = 200991310190001583777666386584336026396217394976427657587912725057234300208;
    uint256 constant IC21y = 827851467750227654767119031356781765186868995881906233837512334755107835146;
    
    uint256 constant IC22x = 14071773315732611409321561699094196761444149346485345405535579982605633045827;
    uint256 constant IC22y = 7542234113899008234925061393213602764636298942978712079838397861309977786153;
    
    uint256 constant IC23x = 2912180444987896567871697567310798366528472296704117928080516627436998760740;
    uint256 constant IC23y = 6629208164180628301167166560286034947732566110993066692051683178730094363992;
    
    uint256 constant IC24x = 249408197259865278389120283867626524202837266718582545964643176251533840397;
    uint256 constant IC24y = 19509489741377523411006583143331463334825861068585118081309125310130370964181;
    
    uint256 constant IC25x = 21666189942620105888584845133532750301305336304488274925062034044831613436367;
    uint256 constant IC25y = 8870970179299946669352209436766178808978865794471917897401849644159201864069;
    
    uint256 constant IC26x = 1411289757543518199013696236037929939541118252244357879173482586722814139169;
    uint256 constant IC26y = 18649187229365585979799858005758755857644449844938803037715087417557102789483;
    
    uint256 constant IC27x = 1133401220838276298211377497391545778943134228367713982590968295153332517510;
    uint256 constant IC27y = 13349968083912790125811009062178007367907535278667963798799369809092117733289;
    
    uint256 constant IC28x = 19272443205426696836128633871301523201203672790024003466623544461569304780410;
    uint256 constant IC28y = 7879590502596659641229634633841853918880386601375891218372985420616206098731;
    
    uint256 constant IC29x = 1372683778040162044675933009024165714500528420620533602081718872673332761975;
    uint256 constant IC29y = 3823865254485459443910338974092038059781751166817816027074526304440570729725;
    
    uint256 constant IC30x = 10943971753480552474999441609877517806875220515243697609052290458748018251648;
    uint256 constant IC30y = 4853241636444729020634422189539023175417338826206263188191994685319992834868;
    
    uint256 constant IC31x = 21502109868934947868298720353036168334360508254497725127282855994468073987288;
    uint256 constant IC31y = 8913741643458248355232328143606990198572112511173670415620830693310533574246;
    
    uint256 constant IC32x = 18472647650435423988489993569200969909541780701310265594007631676231456093046;
    uint256 constant IC32y = 10882905819751359996816464136423938527137703116528724089231575598460826925115;
    
    uint256 constant IC33x = 7768797412589034408360709306871553289522457154582427305028850864414640671601;
    uint256 constant IC33y = 3554384618795721041126452035507654844704083893353615146164313243494908068407;
    
    uint256 constant IC34x = 2031196447113222945689377001658771942927685415270476656516796342090551220223;
    uint256 constant IC34y = 21238190352176672044078257171072542757066393615982963520769609430699309130635;
    
    uint256 constant IC35x = 9546512802044112642721897682487149634302078995399689544472820717378878266006;
    uint256 constant IC35y = 4819735583973592169767260055827546471006203997481054109565737634672119046040;
    
    uint256 constant IC36x = 17237301017348558188491168091391905081939118331743509826922351857627096191423;
    uint256 constant IC36y = 8438597612411308916682794165755771354256739159104379946116495307830811874667;
    
    uint256 constant IC37x = 9031549167872838353359925557517964233587661058313384002245857976964343645036;
    uint256 constant IC37y = 9453804948394201836914257134642119637888749667991999804552679539912873210880;
    
    uint256 constant IC38x = 16572918732763109541164435888616178138852801130775514008923928973300101932461;
    uint256 constant IC38y = 11199405130306704071664619297686464618650396360112963202851387394037760188812;
    
    uint256 constant IC39x = 6246811048066422847561635952175387161132731751551667285693426476262311182501;
    uint256 constant IC39y = 21036782530677734616825137295634387645361438306615817225022660846692676283251;
    
    uint256 constant IC40x = 7298032099211022741122071725780952807121474383588885266502017816223181503497;
    uint256 constant IC40y = 9373593407628415166832505209491570681119331917864436978281179471889039059641;
    
    
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

        public_inputs[0] = 11210484740205373072232406180095151368180923534905965420408063074878474947242;
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
}