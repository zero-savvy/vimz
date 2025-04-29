// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {IERC4907} from "./IERC4907.sol";
import {IERC721} from "openzeppelin-contracts/token/ERC721/IERC721.sol";
import {LicenseToken} from "./LicenseToken.sol";

interface IImageGateway {
    function isRootImage(uint256 imageHash) external view returns (bool);

    function isForCommercialUse(uint256 imageHash) external view returns (bool);

    function imageOwner(uint256 rootHash) external view returns (address);

    function approvedOperator(uint256 rootHash) external view returns (address);

    function transferOwnership(uint256 rootHash, address newOwner) external;
}

interface ILicenseToken is IERC4907 {
    function mint(
        uint256 itemId,
        address itemOwner,
        uint256 licenseTokenId,
        address licensedUser,
        uint64 expires
    ) external;
}

interface IImageCollection is IERC721 {
    function mint(address owner, uint256[] calldata roots) external returns (uint256);
}

contract Marketplace {
    // ------------------------------------ TYPES ------------------------------------ //

    struct Bid {
        uint256 price;
        address seller;
    }

    struct LicensePricing {
        address owner;
        uint256 perBlock;
        uint64 minDuration;
    }

    // ------------------------------------ STORAGE ------------------------------------ //

    IImageGateway    public immutable gateway;
    ILicenseToken    public immutable licence;
    IImageCollection public immutable collection;

    mapping(uint256 => Bid)            public ownershipBids;
    mapping(uint256 => LicensePricing) public licencePrice;
    mapping(uint256 => uint256)        public licenseTokens;

    uint256 private licenseNonce;

    // ------------------------------------ CONSTRUCTORS ------------------------------------ //

    constructor(address imageGateway, address imageLicenseToken, address imageCollection) {
        gateway = IImageGateway(imageGateway);
        licence = ILicenseToken(imageLicenseToken);
        collection = IImageCollection(imageCollection);
    }

    // ------------------------------------ OWNERSHIP TRADING ------------------------------------ //

    function listImage(uint256 imageHash, uint256 price) external {
        require(ownershipBids[imageHash].seller == address(0), "Image already listed");
        require(gateway.isRootImage(imageHash), "Not a root image");
        require(gateway.imageOwner(imageHash) == msg.sender, "Only owner can list image for sale");
        ownershipBids[imageHash] = Bid(price, msg.sender);
    }

    function cancelListing(uint256 imageHash) external {
        Bid storage bid = ownershipBids[imageHash];
        require(bid.seller == msg.sender, "Only seller can cancel listing");
        delete ownershipBids[imageHash];
    }

    function buyImage(uint256 imageHash) external payable {
        Bid storage bid = ownershipBids[imageHash];

        require(bid.seller != address(0), "Image is not listed for sale");
        require(bid.price == msg.value, "Incorrect token amount");
        require(gateway.approvedOperator(imageHash) == address(this), "Marketplace is not approved operator");

        delete ownershipBids[imageHash];
        gateway.transferOwnership(imageHash, msg.sender);

        (bool success,) = bid.seller.call{value: msg.value}("");
        require(success, "Ownership transfer failed");
    }

    // ------------------------------------ TIMED COMMERCIAL LICENSING ------------------------------------ //

    function setLicencePrice(uint256 imageHash, uint256 perBlock, uint64 minDuration) external {
        require(gateway.isRootImage(imageHash), "Not a root image");
        require(gateway.isForCommercialUse(imageHash), "Image is not for commercial use");

        address owner = gateway.imageOwner(imageHash);
        require(owner == msg.sender, "Only owner can set license price");

        licencePrice[imageHash] = LicensePricing(owner,perBlock, minDuration);
    }

    function setCollectionLicensePrice(
        uint256[] calldata imageHashes,
        uint256 perBlock,
        uint64 minDuration
    ) external {
        address owner = gateway.imageOwner(imageHashes[0]);
        require(msg.sender == owner, "Only owner can set license price");

        for (uint i; i < imageHashes.length; ++i) {
            require(gateway.isRootImage(imageHashes[i]), "Not a root image");
            require(gateway.isForCommercialUse(imageHashes[i]), "Image is not for commercial use");
            require(gateway.imageOwner(imageHashes[i]) == owner, "Collection images must have the same owner");
        }

        uint256 key = uint256(keccak256(abi.encodePacked(imageHashes)));
        licencePrice[key] = LicensePricing(owner, perBlock, minDuration);
    }

    function buyTimedLicence(uint256 itemId, uint64 blocksDuration) external payable {
        LicensePricing memory pricing = licencePrice[itemId];
        require(blocksDuration >= pricing.minDuration, "License duration too short");

        uint256 cost = uint256(blocksDuration) * pricing.perBlock;
        require(cost == msg.value, "Incorrect payment amount");

        uint256 tokenId = uint256(keccak256(abi.encodePacked(itemId, ++licenseNonce)));
        licenseTokens[tokenId] = itemId;

        licence.mint(itemId, pricing.owner, tokenId, msg.sender, uint64(block.number) + blocksDuration);

        (bool success,) = pricing.owner.call{value: msg.value}("");
        require(success, "License payment transfer failed");
    }

    function extendLicence(uint256 licenseTokenId, uint64 addBlocks) external payable {
        require(licence.userOf(licenseTokenId) == msg.sender, "Caller is not the license user");

        uint64 oldExpiration = licence.userExpires(licenseTokenId);
        require(oldExpiration > block.number, "License already expired");

        uint256 itemId = licenseTokens[licenseTokenId];
        LicensePricing memory pricing = licencePrice[itemId];

        uint256 cost = uint256(addBlocks) * pricing.perBlock;
        require(msg.value == cost, "Incorrect payment amount");

        licence.setUser(licenseTokenId, msg.sender, oldExpiration + addBlocks);

        (bool success,) = pricing.owner.call{value: msg.value}("");
        require(success, "License payment transfer failed");
    }
}
