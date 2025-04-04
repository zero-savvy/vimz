// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import "./CreatorRegistry.sol";
import "./DeviceRegistry.sol";
import "./Licensing.sol"; // Contains the LicenseType enum and/or License struct

/**
 * @dev A unified asset structure.
 * For an Original asset, captureTime and device are set.
 * For an Edited asset, sourceAssetId (pointer to the source asset) and transformation
 * describe the edit. Proofs are not stored.
 */
struct Asset {
    address creator;       // Creator's address.
    uint256 imageHash;     // Hash of the asset data.
    uint256 captureTime;   // Unix timestamp when the image was captured (for originals).
    License license;       // Licensing details.
    address device;        // Capturing device address (for originals).
    uint256 timestamp;     // Registration timestamp.
    uint256 sourceAssetId; // For edited assets: pointer to the source asset; 0 if not applicable.
    string transformation; // For edited assets: description of the applied transformation.
}

/**
 * @title AssetGateway
 * @dev Main entry point for registering assets in the marketplace.
 */
contract AssetGateway {
    CreatorRegistry public creatorRegistry;
    DeviceRegistry public deviceRegistry;

    uint256 public assetCount;

    // Mapping from asset ID to Asset details.
    mapping(uint256 => Asset) public assets;

    event AssetRegistered(
        uint256 indexed assetId,
        address indexed creator,
        uint256 imageHash,
        uint256 captureTime,
        License license,
        address device,
        uint256 sourceAssetId,
        string transformation,
        uint256 timestamp
    );

    /**
     * @notice Constructor initializes the contract with the CreatorRegistry and DeviceRegistry.
     * @param _creatorRegistry Address of the deployed CreatorRegistry contract.
     * @param _deviceRegistry Address of the deployed DeviceRegistry contract.
     */
    constructor(address _creatorRegistry, address _deviceRegistry) {
        creatorRegistry = CreatorRegistry(_creatorRegistry);
        deviceRegistry = DeviceRegistry(_deviceRegistry);
    }

    /**
     * @notice Registers a new original asset captured by a verified device.
     * @param creator The address of the asset creator.
     * @param imageHash The uint256 hash of the original image.
     * @param captureTime Unix timestamp when the image was captured.
     * @param license The licensing details for the asset.
     * @param deviceId The address of the device that captured the image.
     * @param deviceSignature The device’s signature over (creator, imageHash, captureTime).
     */
    function registerNewAsset(
        address creator,
        uint256 imageHash,
        uint256 captureTime,
        License license,
        address deviceId,
        bytes calldata deviceSignature
    ) external {
        // Ensure the creator is verified.
        require(creatorRegistry.verifyCreator(creator), "Creator not verified");

        // Create a message hash for signature verification.
        bytes32 messageHash = keccak256(abi.encodePacked(creator, imageHash, captureTime));

        // Verify the device's signature.
        require(
            deviceRegistry.verifyDeviceSignature(messageHash, deviceSignature, deviceId),
            "Invalid device signature"
        );

        // Increment asset count and store the original asset.
        assetCount++;
        assets[assetCount] = Asset({
            creator: creator,
            imageHash: imageHash,
            captureTime: captureTime,
            license: license,
            device: deviceId,
            timestamp: block.timestamp,
            sourceAssetId: 0,        // Not applicable for originals.
            transformation: ""       // No transformation description.
        });

        emit AssetRegistered(
            assetCount,
            creator,
            imageHash,
            captureTime,
            license,
            deviceId,
            0,
            "",
            block.timestamp
        );
    }

    /**
     * @notice Retrieves details for a given asset by its ID.
     * @param assetId The asset's unique ID.
     * @return The asset's full details.
     */
    function getAsset(uint256 assetId) external view returns (Asset memory) {
        require(assetId > 0 && assetId <= assetCount, "Asset does not exist");
        return assets[assetId];
    }
}
