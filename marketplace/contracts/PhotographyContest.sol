// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {Transformation} from "./Utils.sol";
import {ReentrancyGuard} from "openzeppelin-contracts/utils/ReentrancyGuard.sol";

/// @notice Set of functions for ensuring image provenance.
interface IImageGateway {
    /// @notice Checks that the image was created using only the permissible transformations.
    /// @param imageHash The hash of the image.
    /// @param permissibleTransformations An array of permissible transformations.
    /// @return `true` if the image was created using only the permissible transformations, `false` otherwise.
    function validateEditChain(uint256 imageHash, Transformation[] calldata permissibleTransformations)
        external
        view
        returns (bool);

    /// @notice Checks that the image was created by a single creator.
    /// @param imageHash The hash of the image.
    /// @param creator The address of the creator.
    /// @return `true` if the image was created by a single creator, `false` otherwise.
    function ensureSoloCreator(uint256 imageHash, address creator) external view returns (bool);
}

/// @notice Organizing a photography contest on the blockchain with verifiable submission provenance.
///
/// Contest admin deploys the contract, funding it with the contest reward. Submissions are accepted during the contest
/// window. For each submission, the image registry is called to check that the chain of editions (from submitted image
/// to its original source) contains only the allowed transformations. After the contest is closed the admin may
/// announce a winner, at which point the reward is transferred to the chosen participant.
contract PhotographyContest is ReentrancyGuard {
    // ------------------------------------ TYPES ------------------------------------ //

    /// @notice Current state of the contest.
    enum State {
        SubmissionsOpen,
        SubmissionsClosed,
        WinnerAnnounced
    }

    // ------------------------------------ STORAGE ------------------------------------ //

    /// @notice Contest administrator address.
    address public immutable admin;
    /// @notice Contest reward amount.
    uint256 public immutable reward;
    /// @notice Address of the image gateway contract.
    IImageGateway public immutable imageGateway;
    /// @notice Array of permissible transformations.
    Transformation[] public permissibleTransformations;

    /// @notice Current state of the contest.
    State public state;
    /// @notice Address of the winner.
    address public winner;

    /// @notice Mapping of image hashes to the addresses of their creators.
    mapping(uint256 => address) public submissions;

    // ------------------------------------ EVENTS ------------------------------------ //

    /// @notice Emitted when the contest is created.
    /// @param admin The address of the contest administrator.
    /// @param reward The amount of the contest reward.
    /// @param permissibleTransformations An array of permissible transformations.
    event ContestCreated(address admin, uint256 reward, Transformation[] permissibleTransformations);

    /// @notice Emitted when a submission is received.
    /// @param creator The address of the creator.
    /// @param imageHash The hash of the submitted image.
    event SubmissionReceived(address creator, uint256 imageHash);

    /// @notice Emitted when the submission window is closed.
    event SubmissionWindowClosed();

    /// @notice Emitted when the winner is announced.
    /// @param imageHash The hash of the winning image.
    /// @param winner The address of the winner.
    /// @param reward The amount of the contest reward.
    event WinnerAnnounced(uint256 imageHash, address winner, uint256 reward);

    // ------------------------------------ MODIFIERS ------------------------------------ //

    /// @notice Modifier to restrict access to admin-only functions.
    modifier onlyAdmin() {
        require(msg.sender == admin, "Only admin may call this function.");
        _;
    }

    // ------------------------------------ PUBLIC API ------------------------------------ //

    /// @notice Constructor sets up the contest.
    /// @param _permissibleTransformations An array of permissible transformations.
    /// @param _imageGateway The address of the image gateway contract.
    constructor(Transformation[] memory _permissibleTransformations, address _imageGateway) payable {
        admin = msg.sender;
        reward = msg.value;
        state = State.SubmissionsOpen;
        permissibleTransformations = _permissibleTransformations;
        imageGateway = IImageGateway(_imageGateway);
        emit ContestCreated(admin, reward, permissibleTransformations);
    }

    /// @notice Allows a registered creator to submit an image for contest. Requirements:
    ///  - The submission window is open.
    ///  - The image has not been submitted before.
    ///  - The image was created and edited only by the participant submitting it.
    ///  - The image was created using only the permissible transformations.
    /// @param imageHash The hash of the image (registered in the Image gateway).
    ///
    /// @dev The contract delegates the check that only permissible transformations were used to obtain the submitted
    /// image to the gateway’s `validateEditChain` function. The contract also checks that the image was created only by
    /// the participant submitting it. This is done also by delegating to the image gateway’s `ensureSoloCreator` function.
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

    /// @notice Admin-only function to close the submission window.
    function closeSubmissions() external onlyAdmin {
        require(state == State.SubmissionsOpen, "Submission window is not open.");
        state = State.SubmissionsClosed;
        emit SubmissionWindowClosed();
    }

    /// @notice Admin-only function for announcing the winner.
    /// @param imageHash The hash of the winning image.
    function announceWinner(uint256 imageHash) external onlyAdmin nonReentrant {
        require(state == State.SubmissionsClosed, "Submission window is not closed.");

        winner = submissions[imageHash];
        require(winner != address(0), "Invalid winning submission.");

        state = State.WinnerAnnounced;
        (bool success,) = winner.call{value: reward}("");
        require(success, "Transfer failed.");

        emit WinnerAnnounced(imageHash, winner, reward);
    }
}
