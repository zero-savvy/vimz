#!/bin/bash

set -eou pipefail

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

# Set the pattern of files you want to process
file_pattern="crop_step.circom"

shopt -s nullglob

# If a second argument is provided, use it as the specific file
if [ "$#" -eq 2 ]; then
    user_provided_file="$2"
    # Check if the provided file exists
    if [ -f "$user_provided_file" ]; then
        file_list=("$user_provided_file")
    else
        echo "Error: Provided file '$user_provided_file' not found."
        exit 1
    fi
else
    # If no specific file is provided, use pattern-matching
    file_list=($file_pattern)
fi

# Iterate over files matching the pattern and run commands
for file in "${file_list[@]}"; do
    # echo "$file"
    if [ -f "$file" ]; then
        echo " "
        echo -e "\033[1;34m==================================================\033[0m"
        echo -e "\033[1;34mProcessing file: $file\033[0m"
        echo -e "\033[1;34m==================================================\033[0m"

        # Start timing
        start_time=$(date +%s.%N)

        circom $file --r1cs --wasm --sym --c
        filename=$(basename -- "$file")
        filename_no_extension="${filename%.*}"
        cpp_directory="${filename_no_extension}_cpp"
        js_directory="${filename_no_extension}_js"
        (
            cd "$cpp_directory" || exit
            echo -e "\033[1;32mRunning make in $cpp_directory\033[0m"
            make
        )
        end_time=$(date +%s.%N)
        elapsed_time=$(echo "$end_time - $start_time" | bc)
        echo -e "\033[1;34mTime taken: $elapsed_time seconds\033[0m"
    fi
done
