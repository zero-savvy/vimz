// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {CreatorRegistry} from "./CreatorRegistry.sol";
import {DeviceRegistry} from "./DeviceRegistry.sol";
import {License} from "./Licensing.sol";
import {OnChainVerification} from "./OnChainVerification.sol";
import {Transformation, Image} from "./Utils.sol";

/**
 * @title ImageGateway
 * @dev Main entry point for registering images in the ecosystem.
 */
contract ImageGateway {
    CreatorRegistry public creatorRegistry;
    DeviceRegistry public deviceRegistry;
    mapping(Transformation => address) public verifiers;

    // Mapping from image hash to image details.
    mapping(uint256 => Image) public images;

    event NewImageRegistered(
        uint256 imageHash,
        address creator,
        uint256 captureTime,
        address device,
        License license,
        uint256 timestamp
    );

    event EditedImageRegistered(
        uint256 imageHash,
        address creator,
        uint256 parentHash,
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
     * @notice Registers a new original image captured by a verified device.
     * @param imageHash The uint256 hash of the original image.
     * @param captureTime Unix timestamp when the image was captured.
     * @param license The licensing details for the image.
     * @param deviceId The address of the device that captured the image.
     * @param deviceSignature The device’s signature over (creator, imageHash, captureTime).
     */
    function registerNewImage(
        uint256 imageHash,
        uint256 captureTime,
        License license,
        address deviceId,
        bytes calldata deviceSignature
    ) external {
        // 1. Ensure the image hash is unique.
        require(images[imageHash].creator == address(0), "Image already registered");

        // 2. Ensure the creator is verified.
        address creator = msg.sender;
        require(creatorRegistry.verifyCreator(creator), "Creator not verified");

        // 3. Create a message hash for device signature verification and validate it.
        bytes32 messageHash = keccak256(abi.encodePacked(creator, imageHash, captureTime));
        require(
            deviceRegistry.verifyDeviceSignature(messageHash, deviceSignature, deviceId),
            "Invalid device signature"
        );

        // 4. Store the image.
        images[imageHash] = Image({
            creator: creator,
            captureTime: captureTime,
            license: license,
            timestamp: block.timestamp,
            parentHash: 0,
            transformation: Transformation.NoTransformation
        });

        emit NewImageRegistered(
            imageHash,
            creator,
            captureTime,
            deviceId,
            license,
            block.timestamp
        );
    }

    /**
     * @notice Registers an edited image.
     * @param editedImageHash The uint256 hash of the edited image.
     * @param parentHash The ID of the original image being edited.
     * @param transformation The transformation applied to the original image.
     * @param transformationParameters The parameters for the transformation (like sharpness factor). For some
     *        transformations (like grayscale), this is ignored.
     * @param proof The SNARK proof for the transformation.
     * @param license The licensing details for the edited image.
     */
    function registerEditedImage(
        uint256 editedImageHash,
        uint256 parentHash,
        Transformation transformation,
        uint256[] calldata transformationParameters,
        uint256[25] calldata proof,
        License license
    ) external {
        // 1. Ensure the image hash is unique.
        require(images[editedImageHash].creator == address(0), "Image already registered");

        // 2. Ensure the creator is verified.
        address creator = msg.sender;
        require(creatorRegistry.verifyCreator(creator), "Creator not verified");

        // 3. Ensure the parent image exists.
        Image storage parent = images[parentHash];
        require(parent.creator != address(0), "Parent image does not exist");

        // 4. Ensure the transformation is valid.
        require(transformation != Transformation.NoTransformation, "Invalid transformation");
        bool validProof = OnChainVerification.verifyTransformationValidity(
            parentHash,
            editedImageHash,
            transformation,
            transformationParameters,
            proof,
            verifiers[transformation]
        );
        require(validProof, "Invalid transformation proof");

        // 5. Ensure license is not violated.
        // TODO

        // 6. Store the image.
        images[editedImageHash] = Image({
            creator: creator,
            captureTime: parent.captureTime,
            license: license,
            timestamp: block.timestamp,
            parentHash: parentHash,
            transformation: transformation
        });

        emit EditedImageRegistered(
            editedImageHash,
            creator,
            parentHash,
            transformation,
            license,
            block.timestamp
        );
    }

    /**
     * @notice Checks that the chain of editions for the given image contains only permissible transformations.
     * @param imageHash The hash of the image to be checked.
     * @param permissibleTransformations An array of allowed Transformation enum values.
     * @return true if the entire chain (from the original image to the one requested) is valid, false otherwise.
     */
    function validateEditChain(uint256 imageHash, Transformation[] calldata permissibleTransformations) external view returns (bool){
        Image memory image = images[imageHash];
        while (image.parentHash != 0) {
            bool found = false;
            for (uint i = 0; i < permissibleTransformations.length; i++) {
                if (image.transformation == permissibleTransformations[i]) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                return false;
            }
            image = images[image.parentHash];
        }
        return true;
    }

    /**
     * @notice Checks that the creator is the same for all images in the chain.
     * @param imageHash The ID of the leaf image to be checked.
     * @param creator The address of the creator to be checked against.
     * @return true if the creator is the same for all images in the chain, false otherwise.
     */
    function ensureSoloCreator(uint256 imageHash, address creator) external view returns (bool) {
        Image memory image;
        while (imageHash != 0) {
            image = images[imageHash];
            if (image.creator != creator) {
                return false;
            }
            imageHash = image.parentHash;
        }
        return true;
    }
}
