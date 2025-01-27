// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// ====================================== VERIFIER API =============================================================

interface ISnarkVerifier {
    function verifyNovaProof(
        uint256[9] calldata i_z0_zi,
        uint256[4] calldata U_i_cmW_U_i_cmE,
        uint256[2] calldata u_i_cmW,
        uint256[3] calldata cmT_r,
        uint256[2] calldata pA,
        uint256[2][2] calldata pB,
        uint256[2] calldata pC,
        uint256[4] calldata challenge_W_challenge_E_kzg_evals,
        uint256[2][2] calldata kzg_proof
    ) external view returns (bool);
}

contract ChallengeHub {
    // ====================================== ASSOCIATED TYPES =========================================================

    enum TransformationType {Blur, Contrast}

    struct Challenge {
        address creator;
        string imageID;
        TransformationType transformationType;
        uint256 reward;
        bool solved;
    }

    // ====================================== STORAGE ==================================================================

    ISnarkVerifier public blurVerifier;
    ISnarkVerifier public contrastVerifier;

    mapping(uint256 => Challenge) public challenges;
    uint256 public challengeCount;

    // ====================================== EVENTS ===================================================================

    event ChallengeCreated(
        uint256 challengeId,
        address creator,
        string imageID,
        TransformationType transformationType,
        uint256 reward
    );
    event ChallengeSolved(uint256 challengeId, address solver, uint256 reward, string solutionID);

    // ====================================== METHODS ==================================================================

    constructor(
        ISnarkVerifier _blurVerifier,
        ISnarkVerifier _contrastVerifier
    ) {
        blurVerifier = _blurVerifier;
        contrastVerifier = _contrastVerifier;
    }

    function createChallenge(string memory _imageID, TransformationType _transformationType) external payable {
        require(msg.value > 0, "Must provide a reward deposit");

        challenges[challengeCount] = Challenge({
            creator: msg.sender,
            imageID: _imageID,
            transformationType: _transformationType,
            reward: msg.value,
            solved: false
        });

        emit ChallengeCreated(challengeCount, msg.sender, _imageID, _transformationType, msg.value);
        challengeCount++;
    }

    function imageId(uint256 challengeId) external view returns (string memory) {
        return challenges[challengeId].imageID;
    }

    function submitSolution(
        uint256[9] calldata i_z0_zi,
        uint256[4] calldata U_i_cmW_U_i_cmE,
        uint256[2] calldata u_i_cmW,
        uint256[3] calldata cmT_r,
        uint256[2] calldata pA,
        uint256[2][2] calldata pB,
        uint256[2] calldata pC,
        uint256[4] calldata challenge_W_challenge_E_kzg_evals,
        uint256[2][2] calldata kzg_proof,
        uint256 challengeId,
        string memory solutionID
    ) external {
        Challenge storage challenge = challenges[challengeId];
        require(!challenge.solved, "Challenge already solved");

        ISnarkVerifier verifier;
        if (challenge.transformationType == TransformationType.Blur) {
            verifier = blurVerifier;
        } else {
            verifier = contrastVerifier;
        }

        bool isValid = verifier.verifyNovaProof(
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
        require(isValid, "Invalid proof");

        challenge.solved = true;

        uint256 reward = challenge.reward;
        challenge.reward = 0; // Prevent reentrancy
        (bool success,) = msg.sender.call{value: reward}("");
        require(success, "Reward transfer failed");

        emit ChallengeSolved(challengeId, msg.sender, reward, solutionID);
    }
}
