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
    /// @notice The only address that can mint new collections
    address private immutable minter;

    // ------------------------------------ MODIFIERS ------------------------------------ //

    /// @notice Only the minter can call the function
    modifier onlyMinter() {
        require(msg.sender == minter, "Not minter");
        _;
    }

    // ------------------------------------ PUBLIC API ------------------------------------ //

    /// @notice Instantiate collection contract
    /// @param _minter Address of the only permitted minter
    constructor(address _minter) ERC721("CollectionPass","CPASS") {
        minter = _minter;
    }

    /// @notice Register a new collection
    /// @param collectionId ID of the new collection
    /// @param owner Collection owner
    /// @param roots Hashes of the **root** images that should be included in the collection
    /// @dev Only the minter can call this function
    function mint(uint256 collectionId, address owner, uint256[] calldata roots) external onlyMinter {
        _safeMint(owner, collectionId);
        collections[collectionId] = CollectionData(roots);
    }
}
