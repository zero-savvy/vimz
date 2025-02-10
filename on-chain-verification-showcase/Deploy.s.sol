// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Script, console} from "forge-std/Script.sol";
import {ChallengeHub, ISnarkVerifier} from "ChallengeHub.sol";
import {NovaDecider as BlurVerifier} from "verifier-contracts/BlurVerifier.sol";
import {NovaDecider as ContrastVerifier} from "verifier-contracts/ContrastVerifier.sol";

contract DeployScript is Script {
    function setUp() public {}

    function run() public {
        vm.startBroadcast();

        ISnarkVerifier blurVerifier = ISnarkVerifier(address(new BlurVerifier()));
        ISnarkVerifier contrastVerifier = ISnarkVerifier(address(new ContrastVerifier()));

        new ChallengeHub(blurVerifier, contrastVerifier);

        vm.stopBroadcast();
    }
}
