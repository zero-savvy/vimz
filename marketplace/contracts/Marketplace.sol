// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {IERC4907} from "./IERC4907.sol";
import {IERC721} from "openzeppelin-contracts/token/ERC721/IERC721.sol";
import {LicenseToken} from "./LicenseToken.sol";
import {ReentrancyGuard} from "openzeppelin-contracts/utils/ReentrancyGuard.sol";

/// @notice Subset of Image Gateway functionality.
interface IImageGateway {
    /// @notice Returns the root hash of the image.
    /// @param imageHash The hash of the image.
    /// @return The root hash of the image.
    function isRootImage(uint256 imageHash) external view returns (bool);

    /// @notice Returns whether the image is for commercial use.
    /// @param imageHash The hash of the image.
    /// @return `true` if the image is for commercial use, `false` otherwise.
    function isForCommercialUse(uint256 imageHash) external view returns (bool);

    /// @notice Returns the owner of the image.
    /// @param rootHash The **root** hash of the image.
    /// @return The address of the owner of the image.
    /// @dev If the address is zero, the image is either not registered or is public good.
    function imageOwner(uint256 rootHash) external view returns (address);

    /// @notice Returns the approved operator for the image.
    /// @param rootHash The **root** hash of the image.
    /// @return The address of the approved operator for the image.
    function approvedOperator(uint256 rootHash) external view returns (address);

    /// @notice Transfers ownership of the image to a new owner.
    /// @param rootHash The **root** hash of the image.
    /// @param newOwner The address of the new owner.
    /// @dev This function can only be called by the approved operator of the image or its owner.
    function transferOwnership(uint256 rootHash, address newOwner) external;
}

/// @notice Interface for minting license tokens.
interface ILicenseToken is IERC4907 {
    /// @notice Mints a new license token.
    /// @param itemId The ID of the item.
    /// @param itemOwner The address of the item owner.
    /// @param licenseTokenId The ID of the license token.
    /// @param licensedUser The address of the licensed user.
    /// @param expires The expiration block number of the license.
    function mint(
        uint256 itemId,
        address itemOwner,
        uint256 licenseTokenId,
        address licensedUser,
        uint256 expires
    ) external;
}

/// @notice Interface for the image collection contract.
interface IImageCollection is IERC721 {
    /// @notice Mints a new image collection.
    /// @param key The key for the collection.
    /// @param owner The address of the collection owner.
    /// @param roots The hashes of the root images in the collection.
    function mint(uint256 key, address owner, uint256[] calldata roots) external;
}

/// @notice Marketplace contract for trading images and licenses.
contract Marketplace is ReentrancyGuard {
    // ------------------------------------ TYPES ------------------------------------ //

    /// @notice Represents a bid for an image ownership.
    /// @param price The price of the bid.
    /// @param seller The address of the seller (current owner).
    struct Bid {
        uint256 price;
        address seller;
    }

    /// @notice Represents the pricing for a temporal license.
    /// @param owner The address of the item (image or collection) owner.
    /// @param perBlock The price per block for the license.
    /// @param minDuration The minimum duration for the license.
    struct LicensePricing {
        address owner;
        uint256 perBlock;
        uint256 minDuration;
    }

    // ------------------------------------ STORAGE ------------------------------------ //

    /// @notice The address of the image gateway contract.
    IImageGateway    public immutable gateway;
    /// @notice The address of the license token contract.
    ILicenseToken    public immutable licence;
    /// @notice The address of the image collection contract.
    IImageCollection public immutable collection;

    /// @notice Maps image hashes to ownership bids.
    mapping(uint256 => Bid)            public ownershipBids;
    /// @notice Maps image hashes to license pricing.
    mapping(uint256 => LicensePricing) public licencePrice;
    /// @notice Maps license token IDs to licensed item IDs.
    mapping(uint256 => uint256)        public licenseTokens;

    /// @notice The nonce for generating unique license token IDs.
    uint256 private licenseNonce;

    // ------------------------------------ CONSTRUCTORS ------------------------------------ //

    /// @notice Instantiates the marketplace contract.
    /// @param imageGateway The address of the image gateway contract.
    /// @param imageLicenseToken The address of the license token contract.
    /// @param imageCollection The address of the image collection contract.
    constructor(address imageGateway, address imageLicenseToken, address imageCollection) {
        gateway = IImageGateway(imageGateway);
        licence = ILicenseToken(imageLicenseToken);
        collection = IImageCollection(imageCollection);
    }

    // ------------------------------------ OWNERSHIP TRADING ------------------------------------ //

    /// @notice Lists an image for sale. Requirements:
    ///  - The image is not already listed for sale.
    ///  - The image is a root image.
    ///  - The caller is the owner of the image.
    /// @param imageHash The hash of the image to be listed.
    /// @param price The price of the image.
    function listImage(uint256 imageHash, uint256 price) external {
        require(ownershipBids[imageHash].seller == address(0), "Image already listed");
        require(gateway.isRootImage(imageHash), "Not a root image");
        require(gateway.imageOwner(imageHash) == msg.sender, "Only owner can list image for sale");
        ownershipBids[imageHash] = Bid(price, msg.sender);
    }

    /// @notice Cancels the listing of an image. Requirements:
    ///  - The image is listed for sale.
    ///  - The caller is the seller (current owner) of the image.
    /// @param imageHash The hash of the image to be unlisted.
    function cancelListing(uint256 imageHash) external {
        Bid storage bid = ownershipBids[imageHash];
        require(bid.seller == msg.sender, "Only seller can cancel listing");
        delete ownershipBids[imageHash];
    }

    /// @notice Buys an image. Requirements:
    ///  - The image is listed for sale.
    ///  - The price is equal to the sent value.
    ///  - The marketplace is the approved operator for the image.
    /// @param imageHash The hash of the image to be bought.
    function buyImage(uint256 imageHash) external payable nonReentrant {
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

    /// @notice Sets the license price for an image. Requirements:
    ///  - The image is a root image.
    ///  - The image is for commercial use.
    ///  - The image is not public good.
    ///  - The caller is the owner of the image.
    /// @param imageHash The hash of the **root** image.
    /// @param perBlock The price per block for the license.
    /// @param minDuration The minimum duration for the license.
    function setLicencePrice(uint256 imageHash, uint256 perBlock, uint256 minDuration) external {
        require(gateway.isRootImage(imageHash), "Not a root image");
        require(gateway.isForCommercialUse(imageHash), "Image is not for commercial use");

        address owner = gateway.imageOwner(imageHash);
        require(owner == msg.sender, "Only owner can set license price");

        licencePrice[imageHash] = LicensePricing(owner,perBlock, minDuration);
    }

    /// @notice Sets the license price for a collection of images. Requirements:
    ///  - The images are root images.
    ///  - The images are for commercial use.
    ///  - The images are not public good.
    ///  - The caller is the owner of the images.
    /// @param imageHashes The hashes of the **root** images.
    /// @param perBlock The price per block for the license.
    /// @param minDuration The minimum duration for the license.
    function setCollectionLicensePrice(
        uint256[] calldata imageHashes,
        uint256 perBlock,
        uint256 minDuration
    ) external nonReentrant {
        address owner = gateway.imageOwner(imageHashes[0]);
        require(msg.sender == owner, "Only owner can set license price");

        for (uint i; i < imageHashes.length; ++i) {
            require(gateway.isRootImage(imageHashes[i]), "Not a root image");
            require(gateway.isForCommercialUse(imageHashes[i]), "Image is not for commercial use");
            require(gateway.imageOwner(imageHashes[i]) == owner, "Collection images must have the same owner");
        }

        uint256 key = uint256(keccak256(abi.encodePacked(imageHashes)));
        collection.mint(key, owner, imageHashes);

        licencePrice[key] = LicensePricing(owner, perBlock, minDuration);
    }

    /// @notice Buys a timed license for an image (or a collection). Requirements:
    ///  - License duration is greater than or equal to the minimum duration.
    ///  - The payment amount is equal to the cost of the license.
    /// @param itemId The ID of the item (image or collection).
    /// @param blocksDuration The duration of the license in blocks.
    function buyTimedLicence(uint256 itemId, uint256 blocksDuration) external payable nonReentrant {
        LicensePricing memory pricing = licencePrice[itemId];
        require(blocksDuration >= pricing.minDuration, "License duration too short");

        uint256 cost = uint256(blocksDuration) * pricing.perBlock;
        require(cost == msg.value, "Incorrect payment amount");

        uint256 tokenId = uint256(keccak256(abi.encodePacked(itemId, ++licenseNonce)));
        licenseTokens[tokenId] = itemId;

        licence.mint(itemId, pricing.owner, tokenId, msg.sender, block.number + blocksDuration);

        (bool success,) = pricing.owner.call{value: msg.value}("");
        require(success, "License payment transfer failed");
    }

    /// @notice Extends the duration of a timed license. Requirements:
    ///  - The caller is the user of the license.
    ///  - The license is not expired.
    ///  - The payment amount is equal to the cost of the extension.
    /// @param licenseTokenId The ID of the license token.
    /// @param addBlocks The number of blocks to extend the license.
    function extendLicence(uint256 licenseTokenId, uint256 addBlocks) external payable {
        require(licence.userOf(licenseTokenId) == msg.sender, "Caller is not the license user");

        uint256 oldExpiration = licence.userExpires(licenseTokenId);
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
