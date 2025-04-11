#!/usr/bin/env bash

set -euo pipefail

########################################################################################################################
#### 1. Set the script directory and check if all required tools are installed #########################################
########################################################################################################################
BASE_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
pushd "$BASE_DIR/../.." > /dev/null
./check-env.sh

########################################################################################################################
#### 2. Helper functions ###############################################################################################
########################################################################################################################
# ------------------------------------------------------------------------
# Function: transform
#
# Usage:
#   transform <base_name> <transformation>
#
# Description:
#   Performs an image transformation using the image-editor command.
#   It automatically uses <base_name>.png as input and writes:
#      - <base_name>-<transformation>.json (transformation output)
#      - <base_name>-<transformation>.png (transformed image)
# ------------------------------------------------------------------------
transform() {
  local base="$1"
  local trans="$2"
  shift 2
  local infile="${BASE_DIR}/${base}.png"
  local json_out="${BASE_DIR}/${base}-${trans}.json"
  local png_out="${BASE_DIR}/${base}-${trans}.png"
  image-editor -i "$infile" -o "$json_out" --save-png "$png_out" "$trans" "$@"
}

# ------------------------------------------------------------------------
# Function: hash_image
#
# Usage:
#   hash_image <base_name>
#
# Description:
#   Computes a hash for an image file. Assumes that the image file is
#   named <base_name>.png and writes the hash to <base_name>.hash.
# ------------------------------------------------------------------------
hash_image() {
  local base="$1"
  local infile="${BASE_DIR}/${base}.png"
  local hash_out="${BASE_DIR}/${base}.hash"
  image-hasher "$infile" "$hash_out"
}

########################################################################################################################
#### 3. Do the transformations #########################################################################################
########################################################################################################################
transform "img1" grayscale
transform "img1" sharpness
transform "img1-sharpness" grayscale
transform "img1" blur

transform "img2" contrast --factor 1.4
transform "img2-contrast" sharpness

########################################################################################################################
#### 4. Compute hash of all the images #################################################################################
########################################################################################################################
hash_image "img1"
hash_image "img1-grayscale"
hash_image "img1-sharpness"
hash_image "img1-sharpness-grayscale"
hash_image "img1-blur"

hash_image "img2"
hash_image "img2-contrast"
hash_image "img2-contrast-sharpness"

########################################################################################################################
#### 5. Come back to the original directory ############################################################################
########################################################################################################################
popd > /dev/null
