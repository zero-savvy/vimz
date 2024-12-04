#!/usr/bin/env bash

set -eou pipefail

# Display usage instructions
usage() {
  echo "Usage: $0 <subfolder> [specific_circuit_file]"
  echo " - <subfolder>: Required. The subfolder containing the circuit files."
  echo " - [specific_circuit_file]: Optional. A specific .circom file to rebuild."
  exit 1
}

# Validate arguments
if [ "$#" -lt 1 ]; then
  usage
fi

# Assign the first argument as the subfolder name
subfolder="$1"

# Navigate to the subfolder
cd "$subfolder" || exit

# Set the pattern for files to process
file_pattern="*.circom"

# Enable nullglob to avoid issues with empty file lists
shopt -s nullglob

# Determine files to process
if [ "$#" -eq 2 ]; then
  specific_file="$2"
  if [ -f "$specific_file" ]; then
    file_list=("$specific_file")
  else
    echo "Error: File '$specific_file' not found."
    exit 1
  fi
else
    file_list=($file_pattern)
fi

# Iterate over and process each file
for file in "${file_list[@]}"; do
  echo -e "\033[1mBuilding circuit: ${file}\033[0m"
  base_name=$(basename "$file" .circom)
  circom "$file" --r1cs --wasm > "${base_name}.compile_log"
done
