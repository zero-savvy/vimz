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
/// to its original source) contains only the allowed transformations. After the contest is closed the admin may
/// announce a winner, at which point the reward is transferred to the chosen participant.
contract PhotographyContest {
    // ------------------------------------ TYPES ------------------------------------ //
    enum State {
        SubmissionsOpen,
        SubmissionsClosed,
        WinnerAnnounced
    }

    struct Submission {
        address creator;
        uint256 assetId;
    }

    // ------------------------------------ STORAGE ------------------------------------ //

    address public admin;
    uint256 public reward;
    State public state;
    address public winner;
    IAssetRegistry public assetRegistry;
    Transformation[] public permissibleTransformations;
    Submission[] public submissions;

    // ------------------------------------ EVENTS ------------------------------------ //

    event ContestCreated(address admin, uint256 reward, Transformation[] permissibleTransformations);
    event SubmissionReceived(address creator, uint256 assetId, uint256 submissionIndex);
    event SubmissionWindowClosed();
    event WinnerAnnounced(uint256 submissionIndex, address winner, uint256 reward);

    // ------------------------------------ MODIFIERS ------------------------------------ //

    modifier onlyAdmin() {
        require(msg.sender == admin, "Only admin may call this function.");
        _;
    }

    // ------------------------------------ PUBLIC API ------------------------------------ //

    /**
     * @notice Constructor sets up the contest.
     * @param _permissibleTransformations An array of permissible transformations.
     * @param _assetRegistry The address of the asset registry contract.
     */
    constructor(
        Transformation[] memory _permissibleTransformations,
        address _assetRegistry
    ) payable {
        admin = msg.sender;
        reward = msg.value;
        state = State.SubmissionsOpen;
        permissibleTransformations = _permissibleTransformations;
        assetRegistry = IAssetRegistry(_assetRegistry);
        emit ContestCreated(admin, reward, permissibleTransformations);
    }

    /**
     * @notice Allows a registered creator to submit an asset.
     * @param assetId The ID of the asset (as registered in the Asset Registry).
     *
     * The contract delegates the check that only permissible transformations were used to obtain the submitted asset
     * to the asset registry’s `validateEditChain` function.
     */
    function submit(uint256 assetId) external {
        require(state == State.SubmissionsOpen, "Submission window is closed.");

        bool validChain = assetRegistry.validateEditChain(assetId, permissibleTransformations);
        require(validChain, "Asset violates contest rules.");

        submissions.push(Submission({
            creator: msg.sender,
            assetId: assetId
        }));

        emit SubmissionReceived(msg.sender, assetId, submissions.length - 1);
    }

    /**
     * @notice Admin-only function to close the submission window.
     */
    function closeSubmissions() external onlyAdmin {
        require(state == State.SubmissionsOpen, "Submission window is not open.");
        state = State.SubmissionsClosed;
        emit SubmissionWindowClosed();
    }

    /**
     * @notice Admin-only function for announcing the winner.
     * @param submissionIndex The index of the winning submission.
     */
    function announceWinner(uint256 submissionIndex) external onlyAdmin {
        require(state == State.SubmissionsClosed, "Submission window is not closed.");
        require(submissionIndex < submissions.length, "Invalid submission index.");

        winner = submissions[submissionIndex].creator;
        state = State.WinnerAnnounced;

        payable(winner).transfer(reward);

        emit WinnerAnnounced(submissionIndex, winner, reward);
    }
}
