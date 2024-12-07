#!/usr/bin/env bash

set -eou pipefail

# Display usage instructions
usage() {
    echo "Usage: $0 <subfolder> [specific_circuit_file]"
    echo " - <subfolder>: Required. The subfolder containing the circuit files to clean."
    echo " - [specific_circuit_file]: Optional. A specific circuit to clean related files for."
    exit 1
}

# Validate arguments
if [ "$#" -lt 1 ]; then
    usage
fi

# Assign the first argument as the subfolder name
subfolder="$1"

# Validate the provided subfolder
if [ ! -d "$subfolder" ]; then
    echo "Error: Subfolder '$subfolder' not found."
    exit 1
fi

# Navigate to the subfolder
cd "$subfolder" || exit

# Define patterns for cleanup
folder_patterns=("*_js" "*_cpp")
file_patterns=("*.r1cs" "*.sym")

# If a specific circuit file is provided
if [ "$#" -eq 2 ]; then
    specific_file="$2"
    if [ -f "$specific_file" ]; then
        # Extract the base name (without extension)
        base_name=$(basename "$specific_file" .circom)
        folder_patterns=("${base_name}_js" "${base_name}_cpp")
        file_patterns=("${base_name}.r1cs" "${base_name}.sym")
    else
        echo "Error: Specific circuit file '$specific_file' not found."
        exit 1
    fi
fi

# Function to remove folders matching patterns
remove_folders() {
    local pattern="$1"
    matching_folders=$(find . -type d -name "$pattern")
    if [ -n "$matching_folders" ]; then
        find . -type d -name "$pattern" -exec rm -r {} +
        echo "Folders matching the pattern '$pattern' removed."
    else
        echo "No folders matching the pattern '$pattern' found."
    fi
}

# Function to remove files matching patterns
remove_files() {
    local pattern="$1"
    matching_files=$(find . -type f -name "$pattern")
    if [ -n "$matching_files" ]; then
        find . -type f -name "$pattern" -exec rm {} +
        echo "Files matching the pattern '$pattern' removed."
    else
        echo "No files matching the pattern '$pattern' found."
    fi
}

# Perform cleanup
for pattern in "${folder_patterns[@]}"; do
    remove_folders "$pattern"
done

for pattern in "${file_patterns[@]}"; do
    remove_files "$pattern"
done
