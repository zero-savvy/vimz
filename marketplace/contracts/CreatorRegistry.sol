// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

/**
 * @title Creator Registry
 * @dev This contract allows the registration of verified content creators.
 *      Only creators with valid KYC can be registered, ensuring that only trusted
 *      actors are permitted to upload and claim ownership of new images.
 */
contract CreatorRegistry {
    // ------------------------------------ TYPES ------------------------------------ //

    /// @dev Struct to hold creator details.
    struct Creator {
        /// Timestamp until which the creator's KYC is valid.
        uint256 kycExpiry;
        /// Contact information for the creator.
        string contactInfo;
        /// Ensures creator existence in mapping
        bool exists;
    }

    // ------------------------------------ STORAGE ------------------------------------ //

    /// @notice Address of the contract administrator (the deployer)
    address public admin;

    /// @notice Set of registered creators identified by their Ethereum addresses.
    mapping(address => Creator) public creators;

    // ------------------------------------ EVENTS ------------------------------------ //

    /// @notice Event emitted when a new creator is registered.
    /// @param creator The Ethereum address of the newly registered creator.
    /// @param kycExpiry The expiration timestamp of the creator's KYC.
    event CreatorRegistered(address indexed creator, uint256 kycExpiry);

    // ------------------------------------ MODIFIERS ------------------------------------ //

    /// @notice Modifier to restrict functions to only the contract administrator.
    modifier onlyAdmin() {
        require(msg.sender == admin, "Not admin");
        _;
    }

    // ------------------------------------ PUBLIC API ------------------------------------ //

    /**
     * @notice Constructor sets the deployer as the contract administrator.
     */
    constructor() {
        admin = msg.sender;
    }

    /**
     * @notice Registers a new verified creator.
     * @dev Only the administrator can register a new creator.
     * @param creatorAddr The Ethereum address of the creator being registered.
     * @param kycExpiry The timestamp indicating when the creator's KYC expires.
     * @param contactInfo The contact information for the creator.
     */
    function registerCreator(
        address creatorAddr,
        uint256 kycExpiry,
        string calldata contactInfo
    ) external onlyAdmin {
        require(!creators[creatorAddr].exists, "Creator already registered");
        require(kycExpiry > block.timestamp, "KYC expiry must be in the future");

        creators[creatorAddr] = Creator({
            kycExpiry: kycExpiry,
            contactInfo: contactInfo,
            exists: true
        });

        emit CreatorRegistered(creatorAddr, kycExpiry);
    }

    /**
     * @notice Verifies whether a creator is registered and their KYC is still valid.
     * @param creatorAddr The Ethereum address of the creator to verify.
     * @return True if the creator is registered and KYC is valid, false otherwise.
     */
    function verifyCreator(address creatorAddr) external view returns (bool) {
        Creator memory creator = creators[creatorAddr];
        return creator.exists && block.timestamp < creator.kycExpiry;
    }
}
