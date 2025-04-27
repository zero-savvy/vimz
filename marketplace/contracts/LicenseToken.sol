// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {ERC721} from "openzeppelin-contracts/token/ERC721/ERC721.sol";
import {IERC165} from "openzeppelin-contracts/utils/introspection/IERC165.sol";
import {IERC4907} from "./IERC4907.sol";

contract LicenseToken is IERC165, ERC721, IERC4907 {
    // ------------------------------------ TYPES ------------------------------------ //

    struct Token {
        uint256 itemId;
        address user;
        uint64 expires;
    }

    // ------------------------------------ STORAGE ------------------------------------ //

    // Mapping from license token id to token itself.
    mapping(uint256 => Token) private tokens;
    // Sole minter and updater.
    address public immutable marketplace;

    // ------------------------------------ MODIFIERS ------------------------------------ //

    /// @notice Restricts access to only the Marketplace contract.
    modifier onlyMarketplace() {
        require(msg.sender == marketplace, "Not marketplace");
        _;
    }

    // ------------------------------------ PUBLIC API ------------------------------------ //

    constructor(address _marketplace) ERC721("ImageLicense", "ILIC"){
        marketplace = _marketplace;
    }

    function mint(
        uint256 itemId,
        address itemOwner,
        uint256 licenseTokenId,
        address licensedUser,
        uint64 expires
    ) external onlyMarketplace {
        _safeMint(itemOwner, licenseTokenId);
        tokens[licenseTokenId] = Token(itemId, licensedUser, expires);
        emit UpdateUser(licenseTokenId, licensedUser, expires);
    }

    // ------------------------------------ ERC4907 API ------------------------------------ //

    function setUser(uint256 licenseTokenId, address licensedUser, uint64 expires) external override onlyMarketplace {
        Token storage token = tokens[licenseTokenId];
        require(token.itemId != 0, "Token does not exist");

        token.user = licensedUser;
        token.expires = expires;

        emit UpdateUser(licenseTokenId, licensedUser, expires);
    }

    function userOf(uint256 licenseTokenId) public view override returns (address) {
        Token storage token = tokens[licenseTokenId];
        return block.number > token.expires ? address(0) : token.user;
    }

    function userExpires(uint256 licenseTokenId) external view returns (uint64) {
        return tokens[licenseTokenId].expires;
    }

    // ------------------------------------ ERC165 API ------------------------------------ //

    function supportsInterface(bytes4 interfaceId) public view override(ERC721, IERC165) returns (bool) {
        return interfaceId == type(IERC4907).interfaceId || super.supportsInterface(interfaceId);
    }
}
