// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {ERC721} from "openzeppelin-contracts/token/ERC721/ERC721.sol";

/// @notice This contract allows the minting of NFTs representing collections of images.
contract ImageCollection is ERC721 {
    // ------------------------------------ TYPES ------------------------------------ //

    /// @notice Represents a set of images (including their derivatives)
    /// @param rootHashes Array of hashes of **root** images
    struct CollectionData {
        uint256[] rootHashes;
    }

    // ------------------------------------ STORAGE ------------------------------------ //

    /// @notice All the registered collections
    mapping(uint256 => CollectionData) private collections;
    /// @notice Collection counter
    uint256 private counter;

    // ------------------------------------ PUBLIC API ------------------------------------ //

    /// @notice Instantiate collection contract
    constructor() ERC721("CollectionPass","CPASS") {}

    /// @notice Register a new collection
    /// @param owner Collection owner
    /// @param roots Hashes of the **root** images that should be included in the collection
    /// @return collectionId ID of the new collection
    function mint(address owner, uint256[] calldata roots) external returns (uint256 collectionId) {
        collectionId = ++counter;
        _safeMint(owner, collectionId);
        collections[collectionId] = CollectionData(roots);
    }
}
