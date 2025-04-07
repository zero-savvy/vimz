#!/usr/bin/env bash

set -euo pipefail

# 1. Set the script directory and check if all required tools are installed
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
pushd "$SCRIPT_DIR/../.." > /dev/null
./check-env.sh

# 2. Compute proofs for all transformations. Assume that all needed data has been
#    generated and is available in the image-data directory.
pushd vimz/

cargo run --release --features light-test --bin vimz -- \
  -f grayscale -w ../circuits/sonobe/grayscale_step_js/grayscale_step.wasm \
  -i "$SCRIPT_DIR/../image-data/img1-grayscale.json" \
  -c ../circuits/sonobe/grayscale_step.r1cs \
  -r HD -b sonobe \
  -o "$SCRIPT_DIR/img1-grayscale.proof" \

#cargo run --release --features light-test --bin vimz -- \
#  -f blur -w ../circuits/sonobe/blur_step_js/blur_step.wasm \
#  -i "$SCRIPT_DIR/../image-data/img1-blur.json" \
#  -c ../circuits/sonobe/blur_step.r1cs \
#  -r HD -b sonobe \
#  -o "$SCRIPT_DIR/img1-blur.proof"

# 3. Come back to the original directory
popd > /dev/null
popd > /dev/null
