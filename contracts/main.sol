pragma solidity >=0.7.0 <0.9.0;
import "@openzeppelin-contracts/contracts/utils/cryptography/ECDSA.sol";
import "./spartan_verifier.sol";

contract MediaAuthenticator {
    address private owner;
    uint256[] public validRoots;
    uint256[] public verifiedPubkeys;
    uint256 public latestChallenge;
    mapping(uint256 => uint256) public verifiedOriginals;
    mapping(uint256 => uint256) public verifiedEdits;
    SpartanVerifier public verifier;

    struct VIMzProof {
        uint256 pA;
        uint256 pB1;
        uint256 pB2;
        uint256 pC;
        uint256[] pubSignals; // assuming pubSignals is an array of uint256
    }
    
    modifier onlyOwner() {
        require(owner == msg.sender);
        _;
    }
        constructor(address spartan_verifier) {
        owner = msg.sender;
        verifier = SpartanVerifier(spartan_verifier);
    }

    function getOwnerOriginal(uint256 value) public view returns (uint256) {
        return verifiedOriginals[value];
    }

    function getOwnerEdit(uint256 value) public view returns (uint256) {
        return verifiedOriginals[verifiedEdits[value]];
    }

    function authenticate(VIMzProof[] memory data, bytes memory sig_alpha, bytes memory sig_owner) public {
        bool proofVerification;
        uint256 h_orig;
        uint256 h_tran;
        uint256 id_tran;
        uint256 id_orig;
        uint256 id_owner;
        address addr;

        for (uint256 i = 0; i < data.length; i++) {
            
            // verify zkSNARK proof
            proofVerification = verifier.verify_proof(data[i]);
            require(proofVerification, "Incorrect Proof!");

            h_orig = data[i].h1;
            h_tran = data[i].h2;

            if (i == 0) {
                address recovered_signer = ECDSA.recover(h_orig, sig_alpha);

                if (verifiedOriginals[h_orig] == 0) {
                    require(verifiedPubkeys[recovered_signer] != 0,
                        "UnAuthorizedPubkey: new original must be signed by verified pubkeys only!");
                    require(recovered_signer != address(0), "ECDSA: invalid signature");
                }

                if (recovered_signer != msg.sender) {
                    bytes32 ownership_msg = keccak256(abi.encodePacked("TRANSFER", h_orig, "TO", msg.sender));
                    address recovered_prev_owner = ECDSA.recover(ownership_msg, sig_owner);
                    require(recovered_prev_owner == recovered_signer, "Previous owner must sign the original!");
                    require(verifiedOriginals[h_orig] == 0 || verifiedOriginals[h_orig] == recovered_prev_owner, "Previous owner must be valid!");
                }

                id_owner = msg.sender;
                id_orig = h_orig;
            } else {
                require(data[i-1].h2 == data[i].h1, 
                    "Edits must be sequencial!");
            }

            verifiedOriginals[id_orig] = id_owner;
            verifiedEdits[id_tran] = id_orig;
        }

        address convertedAddress = address(uint160(_pubSignals[1]));
        
        // check authenticity of the device address
        if (convertedAddress != msg.sender)
            { revert(); } 

        // check validity of the Merkle root
        if (!checkRoot(_pubSignals[0])) 
            { revert(); } 

        // check if the challenge is up-to-date
        if (_pubSignals[2] != latestChallenge) 
            { revert(); }
        
        // verify zkSNARK proof
        bool proofVerification;
        proofVerification = verifier.verifyProof(_pA, [_pB1, _pB2], _pC, _pubSignals);    
        if (!proofVerification)
            { revert(); }
    }

    function add_pubkey(uint256 pubkey) external onlyOwner {
        authorizedPubkeys.push(pubkey);
        return; 
    }
}