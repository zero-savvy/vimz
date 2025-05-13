// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {OnChainVerification} from "./OnChainVerification.sol";
import {Transformation} from "./Utils.sol";
import {ReentrancyGuard} from "openzeppelin-contracts/utils/ReentrancyGuard.sol";

/// @notice Bounty program for detecting image infringements.
contract AttributionClaim is ReentrancyGuard {
    // ------------------------------------ TYPES ------------------------------------ //

    /// @notice Bounty set for an image
    /// @param owner Bounty maintainer
    /// @param reward Reward for a single successful violation report
    /// @param pool All available funds for paying out the rewards
    struct Bounty {
        address owner;
        uint256 reward;
        uint256 pool;
    }

    /// @notice Infringement report
    /// @param claimant The reporter address
    /// @param rootHash Hash of the **root** image which was used inappropriately
    /// @param stake Locked reporter funds (SPAM protection)
    /// @param deadline Lock time, when any off-chain dispute may happen
    /// @param evidenceURI Pointer to any relevant report data
    /// @param resolved Marker if the claim has been already resolved
    struct Claim {
        address claimant;
        uint256 rootHash;
        uint256 stake;
        uint256 deadline;
        bytes32 evidenceURI;
        bool resolved;
    }

    // ------------------------------------ STORAGE ------------------------------------ //

    /// @notice Time window for any off-chain dispute
    uint256 public constant RESOLUTION_WINDOW = 7 days;

    /// @notice Mapping between supported image transformations and corresponding verifier contracts.
    mapping(Transformation => address) public verifiers;

    /// @notice Opened bounties
    mapping(uint256 => Bounty) public bounties;
    /// @notice Reported infringements
    mapping(uint256 => Claim) public claims;
    /// @notice Claim counter
    uint256 private counter;
    /// @notice Required report deposit (SPAM protection)
    uint256 public stake;

    // ------------------------------------ EVENTS ------------------------------------ //

    /// @notice Emitted when a bounty receives new funds for paying out rewards
    /// @param owner The bounty maintainer
    /// @param rootHash Hash of the **root** image for which we seek infringement reports
    /// @param pool Current bounty pool
    /// @param rewardPerReport Reward for a single successful report
    event BountyCharged(address owner, uint256 rootHash, uint256 pool, uint256 rewardPerReport);

    /// @notice Emitted when a new infringement is reported
    /// @param claimId ID of the new claim
    /// @param rootHash Hash of the **root** image which rights were violated
    /// @param claimant Reporter
    event ClaimOpened(uint256 claimId, uint256 rootHash, uint256 leaf, address claimant);

    /// @notice Emitted when a claim is resolved
    /// @param claimId ID of the resolved claim
    event ClaimResolved(uint256 claimId);

    // ------------------------------------ PUBLIC API ------------------------------------ //

    /// @notice Instantiate the contract with required report stake and transformation verifiers.
    /// @param _stake Required deposit for reporting an infringement
    /// @param _verifiers Addresses of the deployed verifier contracts. Their order should match `Transformation`
    /// enum variants declaration order.
    constructor(uint256 _stake, address[8] memory _verifiers) {
        stake = _stake;

        verifiers[Transformation.Blur] = _verifiers[0];
        verifiers[Transformation.Brightness] = _verifiers[1];
        verifiers[Transformation.Contrast] = _verifiers[2];
        verifiers[Transformation.Crop] = _verifiers[3];
        verifiers[Transformation.Grayscale] = _verifiers[4];
        verifiers[Transformation.Redact] = _verifiers[5];
        verifiers[Transformation.Resize] = _verifiers[6];
        verifiers[Transformation.Sharpness] = _verifiers[7];
    }

    /// @notice Add new funds to a bounty
    /// @param rootHash Hash of the **root** image for which we seek any rights violation
    /// @param rewardPerReport Reward for a single successful infringement report
    function chargeBounty(uint256 rootHash, uint256 rewardPerReport) external payable {
        require(rewardPerReport != 0, "Bad reward");

        Bounty storage bounty = bounties[rootHash];

        if (bounty.owner == address(0)) {
            bounty.owner = msg.sender;
        } else {
            require(bounty.owner == msg.sender, "Bounty can be charged only by its maintainer");
        }

        bounty.reward = rewardPerReport;
        bounty.pool += msg.value;
        emit BountyCharged(msg.sender, rootHash, bounty.pool, rewardPerReport);
    }

    /// @notice Report an infringement. Requirements:
    ///  - There must be a valid open bounty for `rootHash`, with enough funds to cover potential reward
    ///  - Unless the transformation is trivial (`NoTransformation`), `proof` must be a valid SNARK for this
    ///  transformation
    /// @param rootHash Hash of the **root** image which rights were violated
    /// @param infringementHash Hash of the image being reported
    /// @param transformation Transformation used to obtain reported image
    /// @param transformationParameters The parameters for the transformation (like sharpness factor). For some
    /// transformations (like grayscale), this is ignored.
    /// @param proof The SNARK proof for the transformation.
    /// @param evidenceURI Pointer to any relevant report data
    function claimInfringement(
        uint256 rootHash,
        uint256 infringementHash,
        Transformation transformation,
        uint256[] calldata transformationParameters,
        uint256[25] calldata proof,
        bytes32 evidenceURI
    ) external payable returns (uint256 id) {
        Bounty storage b = bounties[rootHash];
        require(b.reward != 0 && b.pool >= b.reward, "No valid bounty available");
        require(msg.value == stake, "Incorrect stake");

        if (transformation != Transformation.NoTransformation) {
            bool validProof = OnChainVerification.verifyTransformationValidity(
                rootHash,
                infringementHash,
                transformation,
                transformationParameters,
                proof,
                verifiers[transformation]
            );
            require(validProof, "Invalid transformation proof");
        }

        id = ++counter;
        claims[id] = Claim({
            claimant: msg.sender,
            rootHash: rootHash,
            stake: msg.value,
            deadline: block.timestamp + RESOLUTION_WINDOW,
            evidenceURI: evidenceURI,
            resolved: false
        });
        b.pool -= b.reward;
        emit ClaimOpened(id, rootHash, infringementHash, msg.sender);
    }

    /// @notice Resolve infringement report successfully. Can be called only by the bounty owner.
    /// @param claimId ID of the claim to be resolved
    function resolveClaim(uint256 claimId) external nonReentrant {
        Claim storage claim = claims[claimId];
        require(!claim.resolved, "Claim already resolved");
        claim.resolved = true;

        require(block.timestamp > claim.deadline, "Claim is not resolvable yet");

        Bounty storage bounty = bounties[claim.rootHash];
        require(msg.sender == bounty.owner, "Only bounty owner can resolve a claim");

        (bool ok,) = claim.claimant.call{value: claim.stake + bounty.reward}("");
        require(ok, "Transfer failed");

        emit ClaimResolved(claimId);
    }

    /// @notice Resolve infringement report as invalid. Can be called only by the bounty owner.
    /// @param claimId ID of the claim to be resolved
    function closeClaim(uint256 claimId) external {
        Claim storage claim = claims[claimId];
        require(!claim.resolved, "Claim already resolved");
        claim.resolved = true;

        require(block.timestamp > claim.deadline, "Claim is not resolvable yet");

        Bounty storage bounty = bounties[claim.rootHash];
        require(msg.sender == bounty.owner, "Only bounty owner can resolve a claim");

        emit ClaimResolved(claimId);
    }
}
