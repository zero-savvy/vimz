// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.10;

import {License} from "./Licensing.sol";

/**
 * @dev A unified asset structure.
 */
struct Asset {
    address creator;               // Creator's address.
    uint256 imageHash;             // Hash of the asset data.
    uint256 captureTime;           // Unix timestamp when the root image was captured (for originals).
    License license;               // Licensing details.
    uint256 timestamp;             // Registration timestamp.
    uint256 parentAssetId;         // For edited assets: pointer to the parent asset; 0 if not applicable.
    Transformation transformation; // For edited assets: description of the applied transformation. For originals: NoTransformation.
}

/**
 * @dev Enum for asset transformations.
 * These are the transformations that can be applied to an asset.
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
    NoTransformation // Used for original assets.
}
