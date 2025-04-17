// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.10;

import {License} from "./Licensing.sol";

/**
 * @dev A unified Image structure.
 */
struct Image {
    address creator;               // Creator's address.
    uint256 captureTime;           // Unix timestamp when the root image was captured (for originals).
    License license;               // Licensing details.
    uint256 timestamp;             // Registration timestamp.
    uint256 parentHash;            // For edited images: pointer to the parent image; 0 if not applicable.
    Transformation transformation; // For edited images: description of the applied transformation. For originals: NoTransformation.
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
