// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {ERC721} from "openzeppelin-contracts/token/ERC721/ERC721.sol";
import {IERC165} from "openzeppelin-contracts/utils/introspection/IERC165.sol";
import {IERC4907} from "./IERC4907.sol";

/// @notice Token representing a temporal license for a commercial image usage.
contract LicenseToken is IERC165, ERC721, IERC4907 {
    // ------------------------------------ TYPES ------------------------------------ //

    /// @notice License token structure.
    /// @param itemId The id of the licensed item (single image or a collection).
    /// @param user The address of the user who has the license.
    /// @param expires The block number when the license expires.
    struct Token {
        uint256 itemId;
        address user;
        uint256 expires;
    }

    // ------------------------------------ STORAGE ------------------------------------ //

    /// @notice Sole minter and updater.
    address public immutable marketplace;
    /// @notice Mapping from license token id to the token itself.
    mapping(uint256 => Token) private tokens;

    // ------------------------------------ MODIFIERS ------------------------------------ //

    /// @notice Restricts access to only the Marketplace contract.
    modifier onlyMarketplace() {
        require(msg.sender == marketplace, "Not marketplace");
        _;
    }

    // ------------------------------------ PUBLIC API ------------------------------------ //

    /// @notice Constructor for the LicenseToken contract.
    constructor(address _marketplace) ERC721("ImageLicense", "ILIC"){
        marketplace = _marketplace;
    }

    /// @notice Mints a new license token.
    /// @param itemId The id of the licensed item (single image or a collection).
    /// @param itemOwner The address of the item owner.
    /// @param licenseTokenId The id of the license token.
    /// @param licensedUser The address of the user who obtained the license.
    /// @param expires The block number when the license expires.
    /// @dev Only the marketplace contract can call this function.
    function mint(
        uint256 itemId,
        address itemOwner,
        uint256 licenseTokenId,
        address licensedUser,
        uint256 expires
    ) external onlyMarketplace {
        _safeMint(itemOwner, licenseTokenId);
        tokens[licenseTokenId] = Token(itemId, licensedUser, expires);
        emit UpdateUser(licenseTokenId, licensedUser, expires);
    }

    // ------------------------------------ ERC4907 API ------------------------------------ //

    /// @inheritdoc IERC4907
    function setUser(uint256 licenseTokenId, address licensedUser, uint256 expires) external override onlyMarketplace {
        Token storage token = tokens[licenseTokenId];
        require(token.itemId != 0, "Token does not exist");

        token.user = licensedUser;
        token.expires = expires;

        emit UpdateUser(licenseTokenId, licensedUser, expires);
    }

    /// @inheritdoc IERC4907
    function userOf(uint256 licenseTokenId) public view override returns (address) {
        Token storage token = tokens[licenseTokenId];
        return block.number > token.expires ? address(0) : token.user;
    }

    /// @inheritdoc IERC4907
    function userExpires(uint256 licenseTokenId) external view returns (uint256) {
        return tokens[licenseTokenId].expires;
    }

    // ------------------------------------ ERC165 API ------------------------------------ //

    /// @inheritdoc IERC165
    function supportsInterface(bytes4 interfaceId) public view override(ERC721, IERC165) returns (bool) {
        return interfaceId == type(IERC4907).interfaceId || super.supportsInterface(interfaceId);
    }
}
