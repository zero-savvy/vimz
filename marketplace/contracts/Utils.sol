// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

/// @notice How editions may be created. Ordered so that larger value means a more permissive policy
/// (monotone upgrade rule).
enum EditionPolicy {
    Sealed,      // 0 - no‐one may register editions
    OnlyOwner,   // 1 - only current root owner may register editions
    Free         // 2 - anyone may register edition
}

/// @notice Global license terms that applies to the entire transformation tree (original image + all derivatives).
/// @param editionPolicy Policy for creating editions
/// @param commercialUse If `true`, then creator willing to sell commercial rights. Otherwise, the image is strictly for
/// non‑commercial usage
/// @param attribution Optional credit line (full text, URL, ...)
struct LicenseTerms {
    EditionPolicy editionPolicy;
    bool commercialUse;
    string attribution;
}

/// @notice The transformations that can be applied to an image.
enum Transformation {
    Blur,
    Brightness,
    Contrast,
    Crop,
    Grayscale,
    Redact,
    Resize,
    Sharpness,
    NoTransformation // Used for original image.
}

/// @notice Image metadata.
/// @param creator Creator's address.
/// @param captureTime Unix timestamp when the root image was captured.
/// @param timestamp Registration timestamp.
/// @param parentHash Pointer to the parent image; self for originals.
/// @param rootHash Pointer to the root image; self for originals.
/// @param transformation Description of the applied transformation. For originals: NoTransformation.
struct Image {
    address creator;
    uint256 captureTime;
    uint256 timestamp;
    uint256 parentHash;
    uint256 rootHash;
    Transformation transformation;
}
