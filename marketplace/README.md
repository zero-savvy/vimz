# On-chain C2PA-like image marketplace (VIMz+Sonobe based)

_This is dev-stage, brief README. Better version will be provided soon._

# Prerequisites

### PyVIMz

From the repository root, run:

```shell
pip install pyvimz/
```

This will install `image-hasher` and `image-editor` commands.

### Other tools

Run `./check-env.sh` from the repository root. Expected output:

```shell
Checking required tools...
✅ All required tools are installed!
```

# Preparing data beforehands

### Contracts

Build all contracts with:
```shell
make compile-contracts
```

You can browse through contract docs with:
```shell
make serve-contract-docs
```
You will be automatically redirected to `http://localhost:3000` in your browser.

### Images and hashes

[`image-data/`](image-data/) contains:

- source and edited images (`*.png` files)
- source and edited image hashes (`*.hash` files)
- input data for proving edition (`*.json` files)
- [`generate-data.sh`](image-data/generate-data.sh) script that can be used for regenerating all the artifacts (
  including applying editions) starting only with original png files

### Proofs

[`proofs/`](proofs/) contains:

- proofs for all edited images from `image-data/` folder (`*.proof` files)
- [`generate-proofs.sh`](proofs/generate-proofs.sh) script that can be used for regenerating all the proofs starting only
  with fully initialized [`image-data/`](image-data/) directory

# SDK

[`vimz_marketplace_sdk`](vimz_marketplace_sdk) is a Python framework for deploying and interacting with the whole smart contract system

# Running scenarios

[`scenarios/`](scenarios/) contains Python scripts that can be used for running different scenarios with the smart contract system. 
Each script is a separate scenario and can be run independently.

You can run scenarios with:
```shell
# Run all scenarios
./run_scenario.sh

# Run a specific scenario
./run_scenario.sh <scenario_name>
```
