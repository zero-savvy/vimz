#!/bin/bash

# Check if an argument (subfolder) is provided
if [ "$#" -lt 1 ]; then
    echo "Error: You must provide a subfolder name."
    exit 1
fi

# Assign the first argument as the subfolder name
subfolder="$1"

# Check if the provided subfolder exists
if [ ! -d "$subfolder" ]; then
    echo "Error: Subfolder '$subfolder' not found."
    exit 1
fi

# Navigate to the subfolder
cd "$subfolder" || exit

# Set the patterns of folders you want to remove
folder_patterns=("*_js" "*_cpp")
file_patterns=("*.r1cs" "*.sym")

# Use find to locate and remove folders matching the patterns
for pattern in "${folder_patterns[@]}"; do
    find . -type d -name "$pattern" -exec rm -r {} +
    echo "Folders matching the pattern '$pattern' removed."
done

# Use find to locate and remove files matching the patterns
for pattern in "${file_patterns[@]}"; do
    find . -type f -name "$pattern" -exec rm {} +
    echo "Files matching the pattern '$pattern' removed."
done