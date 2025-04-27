// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.10;

/**
 * @dev How editions may be created. Ordered so that larger value means a more permissive policy
 *      (monotone upgrade rule).
 */
enum EditionPolicy {
    Sealed,      // 0 - no‐one may register editions
    OnlyOwner,   // 1 - only current root owner may register editions
    Free         // 2 - anyone may register edition
}

/**
 * @dev Global license that applies to an entire transformation tree (original image + all derivatives).
 */
struct LicenseTerms {
    EditionPolicy editionPolicy; // Policy for creating editions
    bool commercialUse;          // true  => creator willing to sell commercial rights
                                 // false => strictly non‑commercial usage
    string attribution;       // optional credit line (full text, URL, ...)
}

/**
 * @dev Enum for image transformations.
 * These are the transformations that can be applied to an image.
 */
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

/**
 * @dev A unified Image structure.
 */
struct Image {
    address creator;               // Creator's address.
    uint256 captureTime;           // Unix timestamp when the root image was captured.
    uint256 timestamp;             // Registration timestamp.
    uint256 parentHash;            // Pointer to the parent image; self for originals.
    uint256 rootHash;              // Pointer to the root image; self for originals.
    Transformation transformation; // For edited images: description of the applied transformation. For originals: NoTransformation.
}
