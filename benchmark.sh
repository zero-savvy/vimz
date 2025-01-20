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

# Run multiple commands in parallel or single command in foreground
run_commands() {
    local commands=("$@")
    local pids=()
    tmp_dir=".tmp_runs"

    if [ "${#commands[@]}" -eq 1 ]; then
        bash -c "${commands[0]}"
    else
        if [ ! -d "$tmp_dir" ]; then
            mkdir -p "$tmp_dir"
        fi

        for i in "${!commands[@]}"; do
            cmd="${commands[i]}"
            dir=".tmp_runs/cmd$((i + 1))"

            if [ ! -d "$dir" ]; then
                mkdir -p "$dir"
            fi

            output_file="output_$(date +%s%N).txt"
            (cd "$dir" && bash -c "$cmd") > "$output_file" 2>&1 &

            pids+=("$!")
        done

        for pid in "${pids[@]}"; do
            wait "$pid"
        done
    fi
}

# Check command-line arguments
if [ $# -lt 2 ]; then
    echo "Usage: $0 <resolution> <command1> [<command2> <command3> ...]"
    exit 1
fi

# Capture resolution and shift arguments
resolution=$1
shift

# Validate resolution argument
if [[ "$resolution" != "HD" && "$resolution" != "4K" ]]; then
    echo "Invalid resolution. Use 'HD' or '4K'."
    exit 1
fi

# Function to decompress .tar.xz files if the JSON file is missing
ensure_json_file() {
    local json_file="$1"
    local tar_file="${json_file%.json}.tar.xz"
    
    if [ "$resolution" == "4K" ] && [ ! -f "$json_file" ] && [ -f "$tar_file" ]; then
        echo "Decompressing $tar_file..."
        tar -xf "$tar_file" -C "$(dirname "$json_file")"
    fi
}

# Define your predefined commands with resolution
grayscale_json="$script_dir/samples/JSON/$resolution/transformation_grayscale.json"
brightness_json="$script_dir/samples/JSON/$resolution/transformation_brightness.json"
sharpness_json="$script_dir/samples/JSON/$resolution/transformation_sharpness.json"
resize_json="$script_dir/samples/JSON/$resolution/transformation_resize.json"
blur_json="$script_dir/samples/JSON/$resolution/transformation_blur.json"
contrast_json="$script_dir/samples/JSON/$resolution/transformation_contrast.json"
crop_json="$script_dir/samples/JSON/$resolution/transformation_crop.json"

ensure_json_file "$grayscale_json"
ensure_json_file "$brightness_json"
ensure_json_file "$sharpness_json"
ensure_json_file "$resize_json"
ensure_json_file "$blur_json"
ensure_json_file "$contrast_json"
ensure_json_file "$crop_json"

grayscale="/usr/bin/time -v vimz -f grayscale -w $script_dir/circuits/grayscale_step_${resolution}_cpp/grayscale_step_${resolution} -o grayscale_${resolution}.json -i $grayscale_json -c $script_dir/circuits/grayscale_step_${resolution}.r1cs -r $resolution"
brightness="/usr/bin/time -v vimz -f brightness -w $script_dir/circuits/brightness_step_${resolution}_cpp/brightness_step_${resolution} -o brightness_${resolution}.json -i $brightness_json -c $script_dir/circuits/brightness_step_${resolution}.r1cs -r $resolution"
sharpness="/usr/bin/time -v vimz -f sharpness -w $script_dir/circuits/sharpness_step_${resolution}_cpp/sharpness_step_${resolution} -o sharpness_${resolution}.json -i $sharpness_json -c $script_dir/circuits/sharpness_step_${resolution}.r1cs -r $resolution"
resize="/usr/bin/time -v vimz -f resize -w $script_dir/circuits/resize_step_${resolution}_cpp/resize_step_${resolution} -o resize_${resolution}.json -i $resize_json -c $script_dir/circuits/resize_step_${resolution}.r1cs -r $resolution"
blur="/usr/bin/time -v vimz -f blur -w $script_dir/circuits/blur_step_${resolution}_cpp/blur_step_${resolution} -o blur_${resolution}.json -i $blur_json -c $script_dir/circuits/blur_step_${resolution}.r1cs -r $resolution"
contrast="/usr/bin/time -v vimz -f contrast -w $script_dir/circuits/contrast_step_${resolution}_cpp/contrast_step_${resolution} -o contrast_${resolution}.json -i $contrast_json -c $script_dir/circuits/contrast_step_${resolution}.r1cs -r $resolution"
crop="/usr/bin/time -v vimz -f fixedcrop -w $script_dir/circuits/optimized_crop_step_${resolution}_cpp/optimized_crop_step_${resolution} -o crop_${resolution}.json -i $crop_json -c $script_dir/circuits/optimized_crop_step_${resolution}.r1cs -r $resolution"

# Prepare the list of commands based on user input
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

# Run the prepared commands
run_commands "${commands[@]}"

rm -rf .tmp_runs
