#!/bin/bash

# Set the directory where you want to search for files
target_directory="."

# Set the pattern of files you want to process
file_pattern="*.circom"

shopt -s nullglob
# Iterate over files matching the pattern and run commands
for file in $file_pattern; do
    echo "$file"
    if [ -f "$file" ]; then
        # Replace the following command with your desired command
        # For example, let's just print the file name here
        echo " "
        echo "=================================================="
        echo -e "\033[1;34mProcessing file: $file\033[0m"
        echo "=================================================="
        circom $file --r1cs --wasm --sym --c --prime vesta
        filename=$(basename -- "$file")
        filename_no_extension="${filename%.*}"
        cpp_directory="${filename_no_extension}_cpp"
        js_directory="${filename_no_extension}_js"
        (
            cd "$cpp_directory" || exit
            make
        )
        
        # Add your commands here
        # Example: Command to perform some operation on the file
        # your_command "$file"
    fi
done
