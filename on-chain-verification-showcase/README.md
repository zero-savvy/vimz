# Proof of provenance - on-chain verification

_A showcase of the on-chain verification of image manipulation proofs using VIMz tool._

## Scenario

The scenario consists of two main actors: the challenger and the solver.
The challenger creates a challenge by publishing an image to IPFS and demanding a certain transformation to be done to it.
The solver downloads the challenge, solves it, uploads the result to IPFS and provides a ZK proof of the transformation validity.
If everything is correct, the solver is rewarded with a reward.

The main process (including verification) is performed on-chain.
The only off-chain part is the image processing and the proof generation.

## Requirements

1. You must be able to run VIMz tool together with its dependencies (like `Rust`, `Python3`, `Circom`, `Node`).
2. Foundry (https://book.getfoundry.sh/getting-started/installation).
3. IPFS (https://docs.ipfs.tech/install/command-line/).
4. Auxiliary tools like `jq`, `xxd`, `cut`.


## Running the scenario

After running `./scenario.sh`, you should see output similar to the following:

```
[2025-01-27 03:49:10] ✅ Anvil node started
[2025-01-27 03:49:11] ✅ Contracts deployed
[2025-01-27 03:49:11] 🚀 Creating challenge
[2025-01-27 03:49:11]   ✅ Challenge uploaded to IPFS with ID: QmRycz7eP5uzA2gjcjgGfFGE1Rou5p9jLamdfzgNR2k2ve
[2025-01-27 03:49:11]   ✅ Challenge created
[2025-01-27 03:49:11] 🚀 Solving challenge
[2025-01-27 03:49:11]   ✅ Found challenge ID: QmRycz7eP5uzA2gjcjgGfFGE1Rou5p9jLamdfzgNR2k2ve
[2025-01-27 03:49:11]   ✅ Challenge fetched from IPFS
[2025-01-27 03:49:25]   ✅ Image processed
[2025-01-27 03:49:25]   ✅ Solution uploaded to IPFS with ID: QmfW3ALNaPqG1gZ3jmAgAMEbe1uVKvGkTDpUv6tMYiuVyV


 ________________________________________________________
                                                         
 ██     ██  ██  ███    ███  ████████   Verifiable  Image
 ██     ██  ██  ████  ████      ███    Manipulation from
  ██   ██   ██  ██ ████ ██     ██      Folded   zkSNARKs
   ██ ██    ██  ██  ██  ██   ███                         
    ███     ██  ██      ██  ████████████ v1.4.0 ████████
 ________________________________________________________
| Selected Backend: Sonobe
| Input file: "../on-chain-verification-showcase/blur.json"
| Output file: Some("../calldata/proof")
| Selected function: Blur
| Circuit file: "../circuits/sonobe/blur_step.r1cs"
| Witness generator: "../circuits/sonobe/blur_step_js/blur_step.wasm"
| Image resolution: HD
| Demo mode: true
 ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
 INFO Prepare input: 143ms
 INFO Prepare folding:Create circuit: 173ms
 INFO Prepare folding:Preprocess Nova: 3.21s
 INFO Prepare folding:Init Nova: 1.85s
 INFO Prepare folding: 5.24s
 INFO Fold input{steps=10}:Fold step{completed=0}: 1.94s
 INFO Fold input{steps=10}:Fold step{completed=1}: 1.98s
 INFO Fold input{steps=10}:Fold step{completed=2}: 2.59s
 INFO Fold input{steps=10}:Fold step{completed=3}: 2.35s
 INFO Fold input{steps=10}:Fold step{completed=4}: 2.48s
 INFO Fold input{steps=10}:Fold step{completed=5}: 2.36s
 INFO Fold input{steps=10}:Fold step{completed=6}: 2.55s
 INFO Fold input{steps=10}:Fold step{completed=7}: 2.34s
 INFO Fold input{steps=10}:Fold step{completed=8}: 2.46s
 INFO Fold input{steps=10}:Fold step{completed=9}: 2.34s
 INFO Fold input{steps=10}: 23.4s
 INFO Verify folded proof: 83.1ms
 INFO Prepare decider: 22.6s
 INFO Generate decider proof: 26.1s
 INFO Save calldata: 44.6ms


[2025-01-27 03:50:44]   ✅ Proof computed
[2025-01-27 03:50:44]   ✅ Solution submitted
[2025-01-27 03:50:44] ✅ Scenario successfully run
[2025-01-27 03:50:44] ✅ Stopped running anvil node
```

You can also connect some frontend explorer.
For example, investigating the chain with Ethernal gives you a nice overview of the transactions and the contract state:

![create-challenge-event.png](screenshots/create-challenge-event.png)
![submit-solution-1.png](screenshots/submit-solution-1.png)
![submit-solution-2.png](screenshots/submit-solution-2.png)

## Known issues

1. For performance reasons (Sonobe is still in the early development phase), the scenario uses a simplified version of the Decider circuit.
2. There is no proper verification whether the images on IPFS are tied to the SNARK proofs.
This could be easily solved by including IPFS ID in the proof or using blob storage natively supported by the target chain.
