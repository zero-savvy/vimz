// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {ERC721} from "openzeppelin-contracts/token/ERC721/ERC721.sol";

contract ImageCollection is ERC721 {
    // ------------------------------------ TYPES ------------------------------------ //

    struct CollectionData {
        uint256[] rootHashes;
    }

    // ------------------------------------ STORAGE ------------------------------------ //

    mapping(uint256 => CollectionData) private collections;
    uint256 private counter;

    // ------------------------------------ PUBLIC API ------------------------------------ //

    constructor() ERC721("CollectionPass","CPASS") {}

    function mint(address owner, uint256[] calldata roots) external returns (uint256 collectionId) {
        collectionId = ++counter;
        _safeMint(owner, collectionId);
        collections[collectionId] = CollectionData(roots);
    }
}
