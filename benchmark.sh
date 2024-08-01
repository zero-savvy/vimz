#!/bin/bash

# Function to extract maximum resident set size from time command output
extract_max_resident_size() {
    local time_output="$1"
    local max_resident_size=$(echo "$time_output" | grep -oP '(?<=Maximum resident set size \(kbytes\): )\d+')
    echo "$max_resident_size"
}

# Initialize variable to store summation
total_max_resident_size=0

# Get the absolute path of the directory where the script resides
script_dir=$(dirname "$(readlink -f "$0")")

# Function to calculate total maximum resident set size
calculate_total_max_resident_size() {
    local max_resident_sizes=("$@")
    for size in "${max_resident_sizes[@]}"; do
        total_max_resident_size=$((total_max_resident_size + size))
    done
}

# Run multiple commands in parallel
run_multiple_commands() {
    local commands=("$@")
    local pids=()
    tmp_dir=".tmp_runs"

    if [ ! -d "$tmp_dir" ]; then
        mkdir -p "$tmp_dir"
    fi

    # Loop through each command
    for i in "${!commands[@]}"; do
        cmd="${commands[i]}"
        dir=".tmp_runs/cmd$((i + 1))"  # Construct directory name based on command index

        # Check if directory exists, if not, create it
        if [ ! -d "$dir" ]; then
            mkdir -p "$dir"
        fi

        # Generate a unique output file name for each command
        output_file="output_$(date +%s%N).txt"

        # Run the command in the background, redirecting output to the output file
        (cd "$dir" && bash -c "$cmd") > "$output_file" 2>&1 &

        # Store PID of background process
        pids+=("$!")
    done

    # Wait for all commands to finish
    for pid in "${pids[@]}"; do
        wait "$pid"
    done
}

# Check command-line argument
if [ $# -lt 1 ]; then
    echo "Usage: $0 <command1> [<command2> <command3> ...]"
    exit 1
fi

# Define your predefined commands here
grayscale="/usr/bin/time -v vimz -f grayscale -w $script_dir/circuits/grayscale_step_cpp/grayscale_step -o grayscale_hd.json -i $script_dir/samples/JSON/HD/transformation_grayscale.json -c $script_dir/circuits/grayscale_step.r1cs -r HD"
brightness="/usr/bin/time -v vimz -f brightness -w $script_dir/circuits/brightness_step_cpp/brightness_step -o brightness_hd.json -i $script_dir/samples/JSON/HD/transformation_brightness.json -c $script_dir/circuits/brightness_step.r1cs -r HD"
sharpness="/usr/bin/time -v vimz -f sharpness -w $script_dir/circuits/sharpness_step_cpp/sharpness_step -o sharpness_hd.json -i $script_dir/samples/JSON/HD/transformation_sharpness.json -c $script_dir/circuits/sharpness_step.r1cs -r HD"
resize="/usr/bin/time -v vimz -f resize -w $script_dir/circuits/resize_step_cpp/resize_step -o resize_hd.json -i $script_dir/samples/JSON/HD/transformation_resize.json -c $script_dir/circuits/resize_step.r1cs -r HD"
blur="/usr/bin/time -v vimz -f blur -w $script_dir/circuits/blur_step_cpp/blur_step -o blur_hd.json -i $script_dir/samples/JSON/HD/transformation_blur.json -c $script_dir/circuits/blur_step.r1cs -r HD"
contrast="/usr/bin/time -v vimz -f contrast -w $script_dir/circuits/contrast_step_cpp/contrast_step -o contrast_hd.json -i $script_dir/samples/JSON/HD/transformation_contrast.json -c $script_dir/circuits/contrast_step.r1cs -r HD"
crop="/usr/bin/time -v vimz -f crop -w $script_dir/circuits/crop_step_js/crop_step.wasm -o crop_hd.json -i $script_dir/samples/JSON/HD/transformation_crop.json -c $script_dir/circuits/crop_step.r1cs -r HD"

commands=()
for arg in "$@"; do
    case $arg in
        "contrast") commands+=("$contrast") ;;
        "crop") commands+=("$crop") ;;
        "grayscale") commands+=("$grayscale") ;;
        "sharpness") commands+=("$sharpness") ;;
        "brightness") commands+=("$brightness") ;;
        "resize") commands+=("$resize") ;;
        "blur") commands+=("$blur") ;;
        *)
            echo "Unknown command: $arg"
            exit 1
            ;;
    esac
done
run_multiple_commands "${commands[@]}"

rm -rf .tmp_runs
