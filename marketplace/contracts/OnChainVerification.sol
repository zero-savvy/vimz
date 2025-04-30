// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {Transformation} from "./Utils.sol";

/// @notice An interface for verifying image transformations on-chain with a VIMz+Sonobe generated verifiers.
library OnChainVerification {
    /// @notice Verifies the validity of an image transformation. Currently, supports only HD resolution preserving
    /// transformations.
    /// @param sourceHash The hash of the source image
    /// @param editionHash The hash of the edited image
    /// @param transformation The type of transformation applied to the image
    /// @param transformationParameters The parameters for the transformation (like sharpness factor). For some
    /// transformations (like grayscale), this is ignored.
    /// @param proof The SNARK proof for the transformation.
    /// @param verifier The address of the SNARK verifier contract
    /// @return `true` if the transformation is valid, `false` otherwise
    function verifyTransformationValidity(
        uint256 sourceHash,
        uint256 editionHash,
        Transformation transformation,
        uint256[] calldata transformationParameters,
        uint256[25] calldata proof,
        address verifier
    ) public view returns (bool) {
        uint256 steps = 720; // For HD resolution preserving transformations.

        if (
            transformation == Transformation.Grayscale ||
            transformation == Transformation.Redact ||
            transformation == Transformation.Resize
        ) {
            require(transformationParameters.length == 0, "Unexpected transformation parameters.");
            return ISnarkVerifierWithIVCLen2(verifier).verifyOpaqueNovaProofWithInputs(
                steps,
                [uint256(0), 0], // Initial state: empty hashes
                [sourceHash, editionHash], // Final state: parent and edited image hashes
                proof
            );
        }

        if (transformation == Transformation.Brightness || transformation == Transformation.Contrast) {
            require(transformationParameters.length == 1, "Invalid transformation parameters - expected transformation factor.");
            return ISnarkVerifierWithIVCLen3(verifier).verifyOpaqueNovaProofWithInputs(
                steps,
                [0, 0, transformationParameters[0]], // Initial state: empty hashes + parameters
                [sourceHash, editionHash, transformationParameters[0]], // Final state: parent and edited image hashes + parameters
                proof
            );
        }

        if (transformation == Transformation.Blur || transformation == Transformation.Sharpness) {
            require(transformationParameters.length == 2, "Invalid transformation parameters - expected final neighbourhood hashes.");
            return ISnarkVerifierWithIVCLen4(verifier).verifyOpaqueNovaProofWithInputs(
                steps,
                [uint256(0), 0, 0, 0], // Initial state: empty hashes
                [sourceHash, editionHash, transformationParameters[0], transformationParameters[1]], // Final state: parent and edited image hashes + neighbourhood hashes
                proof
            );
        }

        revert ("Unsupported transformation");
    }
}

/// @notice Interface for the SNARK verifiers with IVC state of length 2.
interface ISnarkVerifierWithIVCLen2 {
    /// @notice Verifies an opaque Nova proof with public inputs.
    /// @param steps The number of steps in the proof
    /// @param initialState The initial IVC state of the proof
    /// @param finalState The final IVC state of the proof
    /// @param proof The SNARK proof
    /// @return `true` if the proof is valid, `false` otherwise
    function verifyOpaqueNovaProofWithInputs(
        uint256 steps,
        uint256[2] calldata initialState,
        uint256[2] calldata finalState,
        uint256[25] calldata proof
    ) external view returns (bool);
}

/// @notice Interface for the SNARK verifiers with IVC state of length 3.
interface ISnarkVerifierWithIVCLen3 {
    /// @notice Verifies an opaque Nova proof with public inputs.
    /// @param steps The number of steps in the proof
    /// @param initialState The initial IVC state of the proof
    /// @param finalState The final IVC state of the proof
    /// @param proof The SNARK proof
    /// @return `true` if the proof is valid, `false` otherwise
    function verifyOpaqueNovaProofWithInputs(
        uint256 steps,
        uint256[3] calldata initialState,
        uint256[3] calldata finalState,
        uint256[25] calldata proof
    ) external view returns (bool);
}

/// @notice Interface for the SNARK verifiers with IVC state of length 4.
interface ISnarkVerifierWithIVCLen4 {
    /// @notice Verifies an opaque Nova proof with public inputs.
    /// @param steps The number of steps in the proof
    /// @param initialState The initial IVC state of the proof
    /// @param finalState The final IVC state of the proof
    /// @param proof The SNARK proof
    /// @return `true` if the proof is valid, `false` otherwise
    function verifyOpaqueNovaProofWithInputs(
        uint256 steps,
        uint256[4] calldata initialState,
        uint256[4] calldata finalState,
        uint256[25] calldata proof
    ) external view returns (bool);
}
