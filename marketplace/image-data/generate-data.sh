#!/usr/bin/env bash

set -euo pipefail

# 1. Set the script directory and check if all required tools are installed
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
pushd "$SCRIPT_DIR/../.." > /dev/null
./check-env.sh

# 2. Compute hash of the source images
image-hasher "$SCRIPT_DIR/img1.png" "$SCRIPT_DIR/img1.hash"

# 3. Do transformations
image-editor \
  -i "$SCRIPT_DIR/img1.png" \
  -o "$SCRIPT_DIR/img1-grayscale.json" \
  --save-png "$SCRIPT_DIR/img1-grayscale.png" \
  grayscale

image-editor \
  -i "$SCRIPT_DIR/img1.png" \
  -o "$SCRIPT_DIR/img1-blur.json" \
  --save-png "$SCRIPT_DIR/img1-blur.png" \
  blur

# 4. Compute hash of the transformed images
image-hasher "$SCRIPT_DIR/img1-grayscale.png" "$SCRIPT_DIR/img1-grayscale.hash"
image-hasher "$SCRIPT_DIR/img1-blur.png" "$SCRIPT_DIR/img1-blur.hash"

# 5. Come back to the original directory
popd > /dev/null
