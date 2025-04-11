// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {Transformation} from "./Utils.sol";

interface IAssetRegistry {
    function validateEditChain(uint256 assetId, Transformation[] calldata permissibleTransformations) external view returns (bool);
}

/// @title Photography Contest
/// @notice Implements a photography contest scenario.
/// Contest admin deploys the contract, funding it with the contest reward. Submissions are accepted during the contest
/// window. For each submission, the asset registry is called to check that the chain of editions (from submitted asset
/// to its original source) contains only the allowed transformations. After the deadline the admin may announce a
/// winner, at which point the reward is transferred to the chosen participant.
contract PhotographyContest {
    address public admin;
    uint256 public deadline;
    uint256 public reward;
    bool public closed;
    address public winner;

    // The asset registry in which assets and their edition chains are registered.
    IAssetRegistry public assetRegistry;

    // List of permissible transformations.
    Transformation[] public permissibleTransformations;

    struct Submission {
        address creator;
        uint256 assetId;
    }

    Submission[] public submissions;

    event SubmissionReceived(address creator, uint256 assetId);
    event WinnerAnnounced(uint256 submissionIndex, address winner, uint256 reward);

    modifier onlyAdmin() {
        require(msg.sender == admin, "Only admin may call this function.");
        _;
    }

    /**
     * @notice Constructor sets up the contest.
     * @param _deadline Unix timestamp after which submissions are no longer accepted.
     * @param _permissibleTransformations An array of permissible transformations.
     * @param _assetRegistry The address of the asset registry contract.
     */
    constructor(
        uint256 _deadline,
        Transformation[] memory _permissibleTransformations,
        address _assetRegistry
    ) payable {
        require(block.timestamp <= _deadline, "Deadline must be in the future.");
        admin = msg.sender;
        deadline = _deadline;
        reward = msg.value;
        permissibleTransformations = _permissibleTransformations;
        assetRegistry = IAssetRegistry(_assetRegistry);
        closed = false;
    }

    /**
     * @notice Allows a registered creator to submit an asset.
     * @param assetId The ID of the asset (as registered in the Asset Registry).
     *
     * The contract delegates the check on the edition chain to the asset registry’s `validateEditChain` function, which
     * verifies that only permissible transformations are present in the chain from the submitted asset back to its root.
     */
    function submit(uint256 assetId) external {
        require(block.timestamp < deadline, "Submission window is closed.");

        bool validChain = assetRegistry.validateEditChain(assetId, permissibleTransformations);
        require(validChain, "Asset chain contains non-permissible transformations.");

        submissions.push(Submission({
            creator: msg.sender,
            assetId: assetId
        }));

        emit SubmissionReceived(msg.sender, assetId);
    }

    /**
     * @notice Admin function for announcing the winner.
     * @param submissionIndex The index of the winning submission.
     */
    function announceWinner(uint256 submissionIndex) external onlyAdmin {
        require(block.timestamp >= deadline, "Submission window is still open.");
        require(!closed, "Contest already closed.");
        require(submissionIndex < submissions.length, "Invalid submission index.");

        winner = submissions[submissionIndex].creator;
        closed = true;

        payable(winner).transfer(reward);

        emit WinnerAnnounced(submissionIndex, winner, reward);
    }
}
