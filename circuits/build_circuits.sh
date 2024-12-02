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

# Validate the provided subfolder
if [ ! -d "$subfolder" ]; then
    echo "Error: Subfolder '$subfolder' not found."
    exit 1
fi

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

# Check if there are any files to process
if [ "${#file_list[@]}" -eq 0 ]; then
    echo "No .circom files found in subfolder '$subfolder'."
    exit 1
fi

# Function to process a single circuit file
process_file() {
    local file="$1"
    echo " "
    echo -e "\033[1;34m==================================================\033[0m"
    echo -e "\033[1;34mProcessing file: $file\033[0m"
    echo -e "\033[1;34m==================================================\033[0m"

    # Start timing
    start_time=$(date +%s.%N)

    circom "$file" --r1cs --wasm --sym --c
    filename=$(basename -- "$file")
    filename_no_extension="${filename%.*}"
    cpp_directory="${filename_no_extension}_cpp"
    js_directory="${filename_no_extension}_js"
    (
        cd "$cpp_directory" || exit
        echo -e "\033[1;32mRunning make in $cpp_directory\033[0m"
        make
    )

    # End timing and report
    end_time=$(date +%s.%N)
    elapsed_time=$(echo "$end_time - $start_time" | bc)
    echo -e "\033[1;34mTime taken: $elapsed_time seconds\033[0m"
}

# Iterate over and process each file
for file in "${file_list[@]}"; do
    process_file "$file"
done
