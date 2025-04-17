// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {Transformation} from "./Utils.sol";

library OnChainVerification {
    function verifyTransformationValidity(
        uint256 sourceHash,
        uint256 editionHash,
        Transformation transformation,
        uint256 transformationParameters,
        uint256[25] calldata proof,
        address verifier
    ) public view returns (bool) {
        uint256 steps = 720; // For HD resolution preserving transformations.

        if (
            transformation == Transformation.Grayscale ||
            transformation == Transformation.Redact ||
            transformation == Transformation.Resize
        ) {
            return ISnarkVerifierWithIVCLen2(verifier).verifyOpaqueNovaProofWithInputs(
                steps,
                [uint256(0), 0], // Initial state: empty hashes
                [sourceHash, editionHash], // Final state: parent and edited image hashes
                proof
            );
        }

        if (transformation == Transformation.Brightness || transformation == Transformation.Contrast) {
            return ISnarkVerifierWithIVCLen3(verifier).verifyOpaqueNovaProofWithInputs(
                steps,
                [0, 0, transformationParameters], // Initial state: empty hashes + parameters
                [sourceHash, editionHash, transformationParameters], // Final state: parent and edited image hashes + parameters
                proof
            );
        }

        if (transformation == Transformation.Blur || transformation == Transformation.Sharpness) {
            return ISnarkVerifierWithIVCLen4(verifier).verifyOpaqueNovaProofWithInputs(
                steps,
                [uint256(0), 0, 0, 0], // Initial state: empty hashes
                [sourceHash, editionHash, 0, 0], // Final state: parent and edited image hashes
                proof
            );
        }

        revert ("Unsupported transformation");
    }
}

/**
 * @dev Interface for the SNARK verifiers with IVC state of length 2.
 */
interface ISnarkVerifierWithIVCLen2 {
    function verifyOpaqueNovaProofWithInputs(
        uint256 steps,
        uint256[2] calldata initial_state,
        uint256[2] calldata final_state,
        uint256[25] calldata proof
    ) external view returns (bool);
}

/**
 * @dev Interface for the SNARK verifiers with IVC state of length 3.
 */
interface ISnarkVerifierWithIVCLen3 {
    function verifyOpaqueNovaProofWithInputs(
        uint256 steps,
        uint256[3] calldata initial_state,
        uint256[3] calldata final_state,
        uint256[25] calldata proof
    ) external view returns (bool);
}

/**
 * @dev Interface for the SNARK verifiers with IVC state of length 4.
 */
interface ISnarkVerifierWithIVCLen4 {
    function verifyOpaqueNovaProofWithInputs(
        uint256 steps,
        uint256[4] calldata initial_state,
        uint256[4] calldata final_state,
        uint256[25] calldata proof
    ) external view returns (bool);
}
