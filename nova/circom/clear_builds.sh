#!/bin/bash

# Set the directory where you want to search for folders
target_directory="."

# Set the patterns of folders you want to remove
folder_patterns=( )

folder_patterns=("*_js" "*_cpp")
file_patterns=("*.r1cs" "*.sym")

# Use find to locate and remove folders matching the patterns
for pattern in "${folder_patterns[@]}"; do
    find "$target_directory" -type d -name "$pattern" -exec rm -r {} +
    echo "Folders matching the pattern '$pattern' removed."
done

# Use find to locate and remove files matching the patterns
for pattern in "${file_patterns[@]}"; do
    find "$target_directory" -type f -name "$pattern" -exec rm {} +
    echo "Files matching the pattern '$pattern' removed."
done