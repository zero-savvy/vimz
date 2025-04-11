#!/usr/bin/env bash

set -euo pipefail

########################################################################################################################
#### 1. Set the script directory and check if all required tools are installed #########################################
########################################################################################################################
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
IMAGE_DATA="${SCRIPT_DIR}/../image-data"
pushd "$SCRIPT_DIR/../.." > /dev/null
./check-env.sh

########################################################################################################################
#### 2. Helper functions ###############################################################################################
########################################################################################################################
# ------------------------------------------------------------------------
# Function: compute_proof
#
# Usage:
#   compute_proof <transformation> <base_name> [extra arguments...]
#
# Description:
#   Automatically computes the proof using the VIMz tool.
#   It assembles all needed paths:
#       - Input file: ${IMAGE_DATA}/${base}-${transformation}.json
#       - Wasm file:  ../circuits/sonobe/${transformation}_step_js/${transformation}_step.wasm
#       - Circuit file: ../circuits/sonobe/${transformation}_step.r1cs
#       - Output file: ${SCRIPT_DIR}/${base}-${transformation}.proof
#
#   It also adds default flags for resolution (-r HD) and backend (-b sonobe)
#   and forwards any extra options to the cargo command.
# ------------------------------------------------------------------------
compute_proof() {
  local base="$1"
  local trans="$2"
  shift 2

  local input_file="${IMAGE_DATA}/${base}-${trans}.json"
  local wasm_file="../circuits/sonobe/${trans}_step_js/${trans}_step.wasm"
  local circuit_file="../circuits/sonobe/${trans}_step.r1cs"
  local output_file="${SCRIPT_DIR}/${base}-${trans}.proof"

  cargo run --release --features light-test --bin vimz -- \
    -f "$trans" \
    -w "$wasm_file" \
    -i "$input_file" \
    -c "$circuit_file" \
    -r HD \
    -b sonobe \
    -o "$output_file" "$@"
}

########################################################################################################################
#### 3. Compute proofs for all transformations. Assume that all needed data has been generated and is available in the #
####    image-data directory.                                                                                          #
########################################################################################################################
pushd vimz/

compute_proof "img1" blur
compute_proof "img1" grayscale
compute_proof "img1" sharpness
compute_proof "img1-sharpness" grayscale

compute_proof "img2" contrast
compute_proof "img2-contrast" sharpness

########################################################################################################################
#### 4. Come back to the original directory ############################################################################
########################################################################################################################
popd > /dev/null
popd > /dev/null
