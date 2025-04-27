// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {IERC4907} from "./IERC4907.sol";

interface IImageGateway {
    function isRootImage(uint256 imageHash) external view returns (bool);

    function imageOwner(uint256 rootHash) external view returns (address);

    function approvedOperator(uint256 rootHash) external view returns (address);

    function transferOwnership(uint256 rootHash, address newOwner) external;
}

interface IImageLicenseToken is IERC4907 {
    function mint(
        uint256 imageHash,
        address imageOwner,
        uint256 licenseTokenId,
        address licensedUser,
        uint64 expires
    ) external;
}

contract Marketplace {
    // ------------------------------------ TYPES ------------------------------------ //

    struct Bid {
        uint256 price;
        address seller;
    }

    struct LicensePricing {
        uint256 perBlock;
        uint64 minBlocks;
    }

    // ------------------------------------ STORAGE ------------------------------------ //

    IImageGateway      public immutable gateway;
    IImageLicenseToken public immutable licence;

    mapping(uint256 => Bid)            public ownershipBids;
    mapping(uint256 => LicensePricing) public licencePrice;
    mapping(uint256 => uint256)        public licenseTokens;

    uint256 private licenseNonce;

    // ------------------------------------ CONSTRUCTORS ------------------------------------ //

    constructor(address imageGateway, address imageLicenseToken){
        gateway = IImageGateway(imageGateway);
        licence = IImageLicenseToken(imageLicenseToken);
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

        (bool success, ) = bid.seller.call{value: msg.value}("");
        require(success, "Transfer failed");
    }
}
