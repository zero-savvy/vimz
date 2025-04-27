// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {CreatorRegistry} from "./CreatorRegistry.sol";
import {DeviceRegistry} from "./DeviceRegistry.sol";
import {OnChainVerification} from "./OnChainVerification.sol";
import {Transformation, Image, LicenseTerms, EditionPolicy} from "./Utils.sol";

/**
 * @title ImageGateway
 * @dev Main entry point for registering images in the ecosystem.
 */
contract ImageGateway {
    // ------------------------------------ STORAGE ------------------------------------ //

    CreatorRegistry public immutable creatorRegistry;
    DeviceRegistry  public immutable deviceRegistry;

    mapping(Transformation => address) public verifiers;

    // Mapping from image hash to image details.
    mapping(uint256 => Image)        public images;
    // Mapping from root image hash to license terms.
    mapping(uint256 => LicenseTerms) public licenses;
    // Mapping from root image hash to owner. Absence (address(0)) means public good
    mapping(uint256 => address)      public owners;
    // Mapping from root image hash to an approved operator who can transfer ownership.
    mapping(uint256 => address)      public approvedOperators;

    // ------------------------------------ EVENTS ------------------------------------ //

    event NewImageRegistered(
        uint256 imageHash,
        address creator,
        uint256 captureTime,
        address device,
        LicenseTerms licenseTerms,
        uint256 timestamp,
        bool isPublicGood
    );

    event EditedImageRegistered(
        uint256 imageHash,
        address creator,
        uint256 parentHash,
        Transformation transformation,
        uint256 timestamp
    );

    event EditionPolicyOpened(uint256 rootHash, EditionPolicy newPolicy);

    event OwnershipTransferred(uint256 rootHash, address oldOwner, address newOwner);

    event OperatorApproved(uint256 rootHash, address operator);

    // ------------------------------------ PUBLIC API ------------------------------------ //

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
     * @param licenseTerms The licensing details for the image.
     * @param deviceId The address of the device that captured the image.
     * @param deviceSignature The device’s signature over (creator, imageHash, captureTime).
     * @param isPublicGood Whether the image is a public good and thus ownership is not transferable.
     */
    function registerNewImage(
        uint256 imageHash,
        uint256 captureTime,
        LicenseTerms calldata licenseTerms,
        address deviceId,
        bytes calldata deviceSignature,
        bool isPublicGood
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

        // 4. Store the image and license terms.
        images[imageHash] = Image({
            creator: creator,
            captureTime: captureTime,
            timestamp: block.timestamp,
            parentHash: imageHash,
            rootHash: imageHash,
            transformation: Transformation.NoTransformation
        });
        licenses[imageHash] = licenseTerms;

        // 5. Ownership assignment.
        if (!isPublicGood) {
            owners[imageHash] = creator;
        } else {
            owners[imageHash] = address(0);
        }

        emit NewImageRegistered(
            imageHash,
            creator,
            captureTime,
            deviceId,
            licenseTerms,
            block.timestamp,
            isPublicGood
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
     */
    function registerEditedImage(
        uint256 editedImageHash,
        uint256 parentHash,
        Transformation transformation,
        uint256[] calldata transformationParameters,
        uint256[25] calldata proof
    ) external {
        // 1. Ensure the image hash is unique.
        require(images[editedImageHash].creator == address(0), "Image already registered");

        // 2. Ensure the creator is verified.
        address creator = msg.sender;
        require(creatorRegistry.verifyCreator(creator), "Creator not verified");

        // 3. Ensure the parent image exists.
        Image storage parent = images[parentHash];
        require(parent.creator != address(0), "Parent image does not exist");

        // 4. Ensure license is not violated.
        LicenseTerms storage terms = licenses[parent.rootHash];
        if (terms.editionPolicy == EditionPolicy.Sealed) revert("Sealed edition policy");
        if (terms.editionPolicy == EditionPolicy.OnlyOwner) {
            require(owners[parent.rootHash] == creator, "Only owner can register editions");
        }

        // 5. Ensure the transformation is valid.
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

        // 6. Store the image.
        images[editedImageHash] = Image({
            creator: creator,
            captureTime: parent.captureTime,
            timestamp: block.timestamp,
            parentHash: parentHash,
            rootHash: parent.rootHash,
            transformation: transformation
        });

        emit EditedImageRegistered(
            editedImageHash,
            creator,
            parentHash,
            transformation,
            block.timestamp
        );
    }

    /**
     * @notice Opens the edition policy for a given image tree.
     * @param rootHash The hash of the root image.
     * @param newPolicy The new edition policy to be set.
     */
    function openEditionPolicy(uint256 rootHash, EditionPolicy newPolicy) external {
        LicenseTerms storage terms = licenses[rootHash];

        require(uint8(newPolicy) > uint8(terms.editionPolicy), "Invalid edition policy upgrade");
        require(owners[rootHash] == msg.sender, "Only owner can open edition policy");

        terms.editionPolicy = newPolicy;
        emit EditionPolicyOpened(rootHash, newPolicy);
    }

    /**
     * @notice Checks that the chain of editions for the given image contains only permissible transformations.
     * @param imageHash The hash of the image to be checked.
     * @param permissibleTransformations An array of allowed Transformation enum values.
     * @return true if the entire chain (from the original image to the one requested) is valid, false otherwise.
     */
    function validateEditChain(uint256 imageHash, Transformation[] calldata permissibleTransformations) external view returns (bool){
        Image storage image = images[imageHash];
        uint256 currentHash = imageHash;

        while (image.parentHash != currentHash) {
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
            currentHash = image.parentHash;
            image = images[currentHash];
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
        Image storage image;
        uint256 currentHash = imageHash;

        while (true) {
            image = images[currentHash];
            if (image.creator != creator) {
                return false;
            }
            if (image.parentHash == currentHash) {
                break;
            }
            currentHash = image.parentHash;
        }
        return true;
    }

    function isRootImage(uint256 imageHash) external view returns (bool) {
        Image storage image = images[imageHash];
        return image.rootHash == imageHash;
    }

    // ------------------------------------ OWNERSHIP ------------------------------------ //

    function imageOwner(uint256 rootHash) external view returns (address) {
        return owners[rootHash];
    }

    function approveOperator(uint256 rootHash, address operator) external {
        require(msg.sender == owners[rootHash], "Only image owner may approve operator");
        require(approvedOperators[rootHash] == address(0), "Some operator already approved");

        approvedOperators[rootHash] = operator;
        emit OperatorApproved(rootHash, operator);
    }

    function approvedOperator(uint256 rootHash) external view returns (address) {
        return approvedOperators[rootHash];
    }

    function transferOwnership(uint256 rootHash, address newOwner) external {
        address oldOwner = owners[rootHash];
        require(
            msg.sender == oldOwner || msg.sender == approvedOperators[rootHash],
            "Only image owner or an approved operator can transfer ownership"
        );

        owners[rootHash] = newOwner;
        emit OwnershipTransferred(rootHash, oldOwner, newOwner);
    }
}
