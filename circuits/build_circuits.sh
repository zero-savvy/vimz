#!/bin/bash

# Set the directory where you want to search for files
target_directory="."

# Set the pattern of files you want to process
file_pattern="*.circom"

shopt -s nullglob

# If an argument is provided, use it as the specific file
if [ "$#" -eq 1 ]; then
    user_provided_file="$1"
    # Check if the provided file exists
    if [ -f "$user_provided_file" ]; then
        file_list=("$user_provided_file")
    else
        echo "Error: Provided file '$user_provided_file' not found."
        exit 1
    fi
else
    # If no argument is provided, use pattern-matching
    file_list=($target_directory/$file_pattern)
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

        circom $file --r1cs --wasm --sym --c --prime vesta
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
