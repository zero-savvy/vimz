// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {OnChainVerification} from "./OnChainVerification.sol";
import {Transformation} from "./Utils.sol";

contract AttributionClaim {
    // ------------------------------------ TYPES ------------------------------------ //

    struct Bounty {
        uint256 reward;
        uint256 pool;
    }

    struct Claim {
        address claimant;
        uint256 rootHash;
        uint256 stake;
        uint64 deadline;
        bytes32 evidenceURI;
        bool resolved;
    }

    // ------------------------------------ STORAGE ------------------------------------ //

    uint256 public constant RESOLUTION_WINDOW = 7 days;

    mapping(Transformation => address) public verifiers;

    mapping(uint256 => Bounty) public bounties;
    mapping(uint256 => Claim) public claims;
    uint256 public counter;
    uint256 public stake;

    // ------------------------------------ EVENTS ------------------------------------ //

    event BountyCharged(uint256 rootHash, uint256 amount, uint256 rewardPerValid);
    event ClaimOpened(uint256 claimId, uint256 rootHash, uint256 leaf, address claimant);
    event ClaimResolved(uint256 claimId);

    /* ------------------------------------------------------------------ */

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

    function chargeBounty(uint256 rootHash, uint256 rewardPerValid) external payable {
        require(rewardPerValid != 0, "Bad reward");

        Bounty storage bounty = bounties[rootHash];
        bounty.reward = rewardPerValid;
        bounty.pool += msg.value;
        emit BountyCharged(rootHash, msg.value, rewardPerValid);
    }

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

        bool validProof = OnChainVerification.verifyTransformationValidity(
            rootHash,
            infringementHash,
            transformation,
            transformationParameters,
            proof,
            verifiers[transformation]
        );
        require(validProof, "Invalid transformation proof");

        id = ++counter;
        claims[id] = Claim({
            claimant: msg.sender,
            rootHash: rootHash,
            stake: msg.value,
            deadline: uint64(block.timestamp + RESOLUTION_WINDOW),
            evidenceURI: evidenceURI,
            resolved: false
        });
        b.pool -= b.reward;
        emit ClaimOpened(id, rootHash, infringementHash, msg.sender);
    }

    function resolveClaim(uint256 id) external {
        Claim storage claim = claims[id];
        require(!claim.resolved, "Claim already resolved");
        claim.resolved = true;

        require(block.timestamp > claim.deadline, "Claim is not resolvable yet");

        Bounty storage bounty = bounties[claim.rootHash];
        (bool ok,) = claim.claimant.call{value: claim.stake + bounty.reward}("");
        require(ok, "Transfer failed");

        emit ClaimResolved(id);
    }
}
