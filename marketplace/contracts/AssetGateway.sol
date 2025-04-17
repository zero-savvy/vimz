// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {CreatorRegistry} from "./CreatorRegistry.sol";
import {DeviceRegistry} from "./DeviceRegistry.sol";
import {License} from "./Licensing.sol";
import {OnChainVerification} from "./OnChainVerification.sol";
import {Transformation, Asset} from "./Utils.sol";

/**
 * @title AssetGateway
 * @dev Main entry point for registering assets in the marketplace.
 */
contract AssetGateway {
    CreatorRegistry public creatorRegistry;
    DeviceRegistry public deviceRegistry;
    mapping(Transformation => address) public verifiers;

    uint256 public assetCount;

    // Mapping from asset ID to Asset details.
    mapping(uint256 => Asset) public assets;

    event NewAssetRegistered(
        uint256 indexed assetId,
        address indexed creator,
        uint256 imageHash,
        uint256 captureTime,
        address device,
        License license,
        uint256 timestamp
    );

    event EditedAssetRegistered(
        uint256 indexed assetId,
        address indexed creator,
        uint256 imageHash,
        uint256 parentAssetId,
        Transformation transformation,
        License license,
        uint256 timestamp
    );

    /**
     * @notice Constructor initializes the contract with the CreatorRegistry and DeviceRegistry.
     * @param _creatorRegistry Address of the deployed CreatorRegistry contract.
     * @param _deviceRegistry Address of the deployed DeviceRegistry contract.
     */
    constructor(address _creatorRegistry, address _deviceRegistry, address[8] memory _verifiers) {
        creatorRegistry = CreatorRegistry(_creatorRegistry);
        deviceRegistry = DeviceRegistry(_deviceRegistry);

        verifiers[Transformation.Blur] = _verifiers[0];
        verifiers[Transformation.Brightness] = _verifiers[1];
        verifiers[Transformation.Contrast] = _verifiers[2];
        verifiers[Transformation.Crop] = _verifiers[3];
        verifiers[Transformation.Grayscale] = _verifiers[4];
        verifiers[Transformation.Redact] = _verifiers[5];
        verifiers[Transformation.Resize] = _verifiers[6];
        verifiers[Transformation.Sharpness] = _verifiers[7];
    }

    /**
     * @notice Registers a new original asset captured by a verified device.
     * @param imageHash The uint256 hash of the original image.
     * @param captureTime Unix timestamp when the image was captured.
     * @param license The licensing details for the asset.
     * @param deviceId The address of the device that captured the image.
     * @param deviceSignature The device’s signature over (creator, imageHash, captureTime).
     */
    function registerNewAsset(
        uint256 imageHash,
        uint256 captureTime,
        License license,
        address deviceId,
        bytes calldata deviceSignature
    ) external {
        // 1. Ensure the creator is verified.
        address creator = msg.sender;
        require(creatorRegistry.verifyCreator(creator), "Creator not verified");

        // 2. Create a message hash for device signature verification and vaildate it.
        bytes32 messageHash = keccak256(abi.encodePacked(creator, imageHash, captureTime));
        require(
            deviceRegistry.verifyDeviceSignature(messageHash, deviceSignature, deviceId),
            "Invalid device signature"
        );

        // 3. Increment asset count and store the original asset.
        assetCount++;
        assets[assetCount] = Asset({
            creator: creator,
            imageHash: imageHash,
            captureTime: captureTime,
            license: license,
            timestamp: block.timestamp,
            parentAssetId: 0,
            transformation: Transformation.NoTransformation
        });

        emit NewAssetRegistered(
            assetCount,
            creator,
            imageHash,
            captureTime,
            deviceId,
            license,
            block.timestamp
        );
    }

    /**
     * @notice Registers an edited asset based on a parent asset.
     * @param editedImageHash The uint256 hash of the edited image.
     * @param parentAssetId The ID of the original asset being edited.
     * @param transformation The transformation applied to the original asset.
     * @param transformationParameters The parameters for the transformation (like sharpness factor). For some
     *        transformations (like grayscale), this is ignored.
     * @param proof The SNARK proof for the transformation.
     * @param license The licensing details for the edited asset.
     */
    function registerEditedAsset(
        uint256 editedImageHash,
        uint256 parentAssetId,
        Transformation transformation,
        uint256 transformationParameters,
        uint256[25] calldata proof,
        License license
    ) external {
        // 1. Ensure the creator is verified.
        address creator = msg.sender;
        require(creatorRegistry.verifyCreator(creator), "Creator not verified");

        // 2. Ensure the parent asset exists.
        require(parentAssetId > 0 && parentAssetId <= assetCount, "Parent asset does not exist");
        Asset storage parent = assets[parentAssetId];

        // 3. Ensure the transformation is valid.
        require(transformation != Transformation.NoTransformation, "Invalid transformation");
        bool validProof = OnChainVerification.verifyTransformationValidity(
            parent.imageHash,
            editedImageHash,
            transformation,
        transformationParameters,
            proof,
            verifiers[transformation]
        );
        require(validProof, "Invalid transformation proof");

        // 4. Ensure license is not violated.
        // TODO

        // 5. Increment asset count and store the asset.
        assetCount++;
        assets[assetCount] = Asset({
            creator: creator,
            imageHash: editedImageHash,
            captureTime: parent.captureTime,
            license: license,
            timestamp: block.timestamp,
            parentAssetId: parentAssetId,
            transformation: transformation
        });

        emit EditedAssetRegistered(
            assetCount,
            creator,
            editedImageHash,
            parentAssetId,
            transformation,
            license,
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

    /**
     * @notice Checks that the chain of editions for the given asset contains only permissible transformations.
     * @param assetId The ID of the asset to be checked.
     * @param permissibleTransformations An array of allowed Transformation enum values.
     * @return true if the entire chain (from the original asset to the `assetId`) is valid, false otherwise.
     */
    function validateEditChain(uint256 assetId, Transformation[] calldata permissibleTransformations)
    external
    view
    returns (bool)
    {
        Asset memory a = assets[assetId];
        while (a.parentAssetId != 0) {
            bool found = false;
            for (uint i = 0; i < permissibleTransformations.length; i++) {
                if (a.transformation == permissibleTransformations[i]) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                return false;
            }
            a = assets[a.parentAssetId];
        }
        return true;
    }
}
