// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {Transformation} from "./Utils.sol";

interface IAssetRegistry {
    function validateEditChain(uint256 assetId, Transformation[] calldata permissibleTransformations) external view returns (bool);

    function ensureSoloCreator(uint256 assetId, address creator) external view returns (bool);
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

    // ------------------------------------ STORAGE ------------------------------------ //

    address public admin;
    uint256 public reward;
    State public state;
    address public winner;
    IAssetRegistry public assetRegistry;
    Transformation[] public permissibleTransformations;
    mapping(uint256 => address) public submissions;

    // ------------------------------------ EVENTS ------------------------------------ //

    event ContestCreated(address admin, uint256 reward, Transformation[] permissibleTransformations);
    event SubmissionReceived(address creator, uint256 assetId);
    event SubmissionWindowClosed();
    event WinnerAnnounced(uint256 assetId, address winner, uint256 reward);

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
     * The contract also checks that the asset was created only by the participant submitting it. This is done also by
     * delegating to the asset registry’s `ensureSoloCreator` function.
     */
    function submit(uint256 assetId) external {
        require(state == State.SubmissionsOpen, "Submission window is closed.");
        require(submissions[assetId] == address(0), "Asset already submitted.");

        bool validCreator = assetRegistry.ensureSoloCreator(assetId, msg.sender);
        require(validCreator, "Participant is not the only creator of the asset.");

        bool validChain = assetRegistry.validateEditChain(assetId, permissibleTransformations);
        require(validChain, "Asset violates contest rules.");

        submissions[assetId] = msg.sender;

        emit SubmissionReceived(msg.sender, assetId);
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
     * @param assetId The winning asset id.
     */
    function announceWinner(uint256 assetId) external onlyAdmin {
        require(state == State.SubmissionsClosed, "Submission window is not closed.");

        winner = submissions[assetId];
        require(winner != address(0), "Invalid winning submission.");

        state = State.WinnerAnnounced;
        payable(winner).transfer(reward);

        emit WinnerAnnounced(assetId, winner, reward);
    }
}
