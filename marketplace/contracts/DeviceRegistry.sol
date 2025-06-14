// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

/// @notice This contract allows trusted camera manufacturers (registrars) to register C2PA-compliant cameras on-chain.
/// The registered devices' keys can later be used to verify the authenticity of cryptographic signatures.
contract DeviceRegistry {
    // ------------------------------------ TYPES ------------------------------------ //

    /// @notice Holds device details
    /// @param registrar The brand that registered this device
    struct Device {
        address registrar;
    }

    // ------------------------------------ STORAGE ------------------------------------ //

    /// @notice Address of the contract administrator (the deployer)
    address public immutable admin;

    /// @notice Set of approved registrars (trusted manufacturers). Only admin can add a registrar, and only registrars
    /// can register devices.
    mapping(address => bool) public registrars;

    /// @notice Mapping of registered devices identified by their public keys (represented by Ethereum addresses)
    mapping(address => Device) public devices;

    // ------------------------------------ EVENTS ------------------------------------ //

    /// @notice Emitted when a new registrar (brand) is added
    /// @param registrar The Ethereum address of the newly added registrar
    event RegistrarAdded(address registrar);

    /// @notice Emitted when a new device (camera) is registered
    /// @param device The public key (represented by an Ethereum address) of the newly registered device
    /// @param registrar The Ethereum address of the manufacturer who registered the device
    event DeviceRegistered(address device, address registrar);

    // ------------------------------------ MODIFIERS ------------------------------------ //

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

    // ------------------------------------ PUBLIC API ------------------------------------ //

    /// @notice Constructor sets the deployer as the contract administrator
    constructor() {
        admin = msg.sender;
    }

    /// @notice Adds a new trusted registrar (camera manufacturer). Only the administrator can add registrars.
    /// @param registrar The Ethereum address of the manufacturer being added
    function registerRegistrar(address registrar) external onlyAdmin {
        require(!registrars[registrar], "Already a registrar");

        registrars[registrar] = true;
        emit RegistrarAdded(registrar);
    }

    /// @notice Registers a new verified camera device. Only an approved registrar can register a new device.
    /// @param devicePubKey The Ethereum address of the device being registered
    function registerDevice(address devicePubKey) external onlyRegistrar {
        require(devices[devicePubKey].registrar == address(0), "Device already registered");
        devices[devicePubKey] = Device({registrar: msg.sender});
        emit DeviceRegistered(devicePubKey, msg.sender);
    }

    /// @notice Verifies whether a given signature was produced by a registered device
    /// @dev Uses Ethereum's `ecrecover` to verify the signer of a message.
    /// @param messageHash The hashed message that was signed
    /// @param signature The cryptographic signature produced by the device
    /// @param deviceAddress The Ethereum address of the device that supposedly signed the message
    /// @return `true` if the signature is valid, `false` otherwise
    function verifyDeviceSignature(bytes32 messageHash, bytes memory signature, address deviceAddress)
        external
        view
        returns (bool)
    {
        require(devices[deviceAddress].registrar != address(0), "Device not found");
        // Recover the signer address from the signature
        address signer = recoverSigner(messageHash, signature);
        // Check if the recovered signer matches the registered device address
        return signer == deviceAddress;
    }

    // ------------------------------------ INTERNALS ------------------------------------ //

    /// @notice Recovers the Ethereum address that signed a given message
    /// @dev Uses `ecrecover`, which is a built-in Solidity function for signature recovery.
    /// @param messageHash The hashed message that was signed
    /// @param signature The cryptographic signature
    /// @return The Ethereum address of the signer
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

        require(v == 27 || v == 28, "Invalid v value");
        // secp256k1 curve order
        uint256 SECP256K1_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141;
        require(uint256(s) <= SECP256K1_N / 2, "s-value too high");

        return ecrecover(messageHash, v, r, s);
    }
}
