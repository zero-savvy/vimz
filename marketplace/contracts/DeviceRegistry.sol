// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

/**
 * @title Device Registry
 * @dev This contract allows trusted camera manufacturers (registrars) to register
 *      C2PA-compliant cameras on-chain. The registered devices' keys can later be used
 *      to verify the authenticity of cryptographic signatures.
 */
contract DeviceRegistry {
    /// @notice Address of the contract administrator (the deployer)
    address public admin;

    /// @notice Set of approved registrars (trusted manufacturers)
    /// @dev Only admin can add a registrar, and only registrars can register devices.
    mapping(address => bool) public registrars;

    /// @notice Mapping of registered devices identified by their public keys (represented by Ethereum addresses)
    mapping(address => Device) public devices;

    /// @dev Struct to hold device details
    struct Device {
        /// The brand that registered this device
        address registrar;
        /// Ensures device existence in mapping
        bool exists;
    }

    /// @notice Event emitted when a new registrar (manufacturer) is added
    /// @param registrar The Ethereum address of the newly added registrar
    event RegistrarAdded(address registrar);

    /// @notice Event emitted when a new device (camera) is registered
    /// @param device The public key (represented by an Ethereum address) of the newly registered device
    /// @param registrar The Ethereum address of the manufacturer who registered the device
    event DeviceRegistered(address device, address indexed registrar);

    /// @notice Restricts access to only the contract administrator
    modifier onlyAdmin() {
        require(msg.sender == admin, "Not admin");
        _;
    }

    /// @notice Restricts access to only approved registrars
    modifier onlyRegistrar() {
        require(registrars[msg.sender], "Not a registrar");
        _;
    }

    /**
     * @notice Constructor sets the deployer as the contract administrator
     */
    constructor() {
        admin = msg.sender; // Assign contract deployer as admin
    }

    /**
     * @notice Adds a new trusted registrar (camera manufacturer)
     * @dev Only the administrator can add registrars.
     * @param registrar The Ethereum address of the manufacturer being added
     */
    function registerRegistrar(address registrar) external onlyAdmin {
        require(!registrars[registrar], "Already a registrar");

        registrars[registrar] = true;
        emit RegistrarAdded(registrar);
    }

    /**
     * @notice Registers a new verified camera device
     * @dev Only an approved registrar can register a new device.
     * @param devicePubKey The Ethereum address of the device being registered
     */
    function registerDevice(address devicePubKey) external onlyRegistrar {
        require(!devices[devicePubKey].exists, "Device already registered");
        devices[devicePubKey] = Device({registrar: msg.sender, exists: true});
        emit DeviceRegistered(devicePubKey, msg.sender);
    }

    /**
     * @notice Verifies whether a given signature was produced by a registered device
     * @dev Uses Ethereum's `ecrecover` to verify the signer of a message.
     * @param messageHash The hashed message that was signed
     * @param signature The cryptographic signature produced by the device
     * @param deviceAddress The Ethereum address of the device that supposedly signed the message
     * @return `true` if the signature is valid, `false` otherwise
     */
    function verifyDeviceSignature(bytes32 messageHash, bytes memory signature, address deviceAddress)
        external
        view
        returns (bool)
    {
        require(devices[deviceAddress].exists, "Device not found");
        // Recover the signer address from the signature
        address signer = recoverSigner(messageHash, signature);
        // Check if the recovered signer matches the registered device address
        return signer == deviceAddress;
    }

    /**
     * @notice Recovers the Ethereum address that signed a given message
     * @dev Uses `ecrecover`, which is a built-in Solidity function for signature recovery.
     * @param messageHash The hashed message that was signed
     * @param signature The cryptographic signature
     * @return The Ethereum address of the signer
     */
    function recoverSigner(bytes32 messageHash, bytes memory signature) private pure returns (address) {
        require(signature.length == 65, "Invalid signature length");

        bytes32 r;
        bytes32 s;
        uint8 v;

        assembly {
            r := mload(add(signature, 32))
            s := mload(add(signature, 64))
            v := byte(0, mload(add(signature, 96)))
        }

        return ecrecover(messageHash, v, r, s);
    }
}
