// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

/**
 * @dev Licensing types for assets.
 */
enum License {
    Closed,         // Only the original creator holds rights.
    Free,           // Free to use, but editions may have restrictions.
    FullyFree,      // Completely free for any use or modification (editions must inherit license).
    FreeForEditions // Creator retains rights to the original, but editions are free.
}
