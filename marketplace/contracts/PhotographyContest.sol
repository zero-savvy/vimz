// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {Transformation} from "./Utils.sol";

interface IImageGateway {
    function validateEditChain(uint256 imageHash, Transformation[] calldata permissibleTransformations) external view returns (bool);

    function ensureSoloCreator(uint256 imageHash, address creator) external view returns (bool);
}

/// @title Photography Contest
/// @notice Implements a photography contest scenario.
/// Contest admin deploys the contract, funding it with the contest reward. Submissions are accepted during the contest
/// window. For each submission, the image registry is called to check that the chain of editions (from submitted image
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
    IImageGateway public imageGateway;
    Transformation[] public permissibleTransformations;
    mapping(uint256 => address) public submissions;

    // ------------------------------------ EVENTS ------------------------------------ //

    event ContestCreated(address admin, uint256 reward, Transformation[] permissibleTransformations);
    event SubmissionReceived(address creator, uint256 imageHash);
    event SubmissionWindowClosed();
    event WinnerAnnounced(uint256 imageHash, address winner, uint256 reward);

    // ------------------------------------ MODIFIERS ------------------------------------ //

    modifier onlyAdmin() {
        require(msg.sender == admin, "Only admin may call this function.");
        _;
    }

    // ------------------------------------ PUBLIC API ------------------------------------ //

    /**
     * @notice Constructor sets up the contest.
     * @param _permissibleTransformations An array of permissible transformations.
     * @param _imageGateway The address of the image gateway contract.
     */
    constructor(
        Transformation[] memory _permissibleTransformations,
        address _imageGateway
    ) payable {
        admin = msg.sender;
        reward = msg.value;
        state = State.SubmissionsOpen;
        permissibleTransformations = _permissibleTransformations;
        imageGateway = IImageGateway(_imageGateway);
        emit ContestCreated(admin, reward, permissibleTransformations);
    }

    /**
     * @notice Allows a registered creator to submit an image for contest.
     * @param imageHash The hash of the image (registered in the Image gateway).
     *
     * The contract delegates the check that only permissible transformations were used to obtain the submitted image
     * to the gateway’s `validateEditChain` function.
     * The contract also checks that the image was created only by the participant submitting it. This is done also by
     * delegating to the image gateway’s `ensureSoloCreator` function.
     */
    function submit(uint256 imageHash) external {
        require(state == State.SubmissionsOpen, "Submission window is closed.");
        require(submissions[imageHash] == address(0), "Image already submitted.");

        bool validCreator = imageGateway.ensureSoloCreator(imageHash, msg.sender);
        require(validCreator, "Participant is not the only creator of the image.");

        bool validChain = imageGateway.validateEditChain(imageHash, permissibleTransformations);
        require(validChain, "Image violates contest rules.");

        submissions[imageHash] = msg.sender;

        emit SubmissionReceived(msg.sender, imageHash);
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
     * @param imageHash The hash of the winning image.
     */
    function announceWinner(uint256 imageHash) external onlyAdmin {
        require(state == State.SubmissionsClosed, "Submission window is not closed.");

        winner = submissions[imageHash];
        require(winner != address(0), "Invalid winning submission.");

        state = State.WinnerAnnounced;
        payable(winner).transfer(reward);

        emit WinnerAnnounced(imageHash, winner, reward);
    }
}
