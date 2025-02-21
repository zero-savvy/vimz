import json
import subprocess
import tempfile
from os import path

import numpy as np
from PIL import Image

########################################################################################################################
####### Environment ####################################################################################################
########################################################################################################################

CIRCUIT_DIR = "./circuits"
CIRCUIT_FILE = f"{CIRCUIT_DIR}/image_running_hash.circom"
CPP_DIR = f"{CIRCUIT_DIR}/image_running_hash_cpp"
WITNESS_GENERATOR = f"{CPP_DIR}/image_running_hash"
INPUT_IMAGE = "source_image/HD.png"


def log(message, **kwargs):
    print(f"\033[1m{message}\033[0m", **kwargs)


def clear_current_log_line():
    print("\r\033[K", end="")


########################################################################################################################
####### Compile the Circom circuit and build the C++ witness generator #################################################
########################################################################################################################
def prepare_witness_generator():
    if path.exists(WITNESS_GENERATOR):
        log(f"Witness generator already exists at {WITNESS_GENERATOR}.")
    else:
        _compile_circuit()
        _build_witness_generator()


def _compile_circuit():
    log("Compiling Circom circuit...", end="", flush=True)
    subprocess.run(["circom", CIRCUIT_FILE, "--O2", "-c", "-o", CIRCUIT_DIR], check=True, stdout=subprocess.DEVNULL)
    log(" Done ✅")


def _build_witness_generator():
    log("Building C++ witness generator...", end="", flush=True)
    subprocess.run(["make", "-C", CPP_DIR], check=True, stdout=subprocess.DEVNULL)
    log(" Done ✅")


########################################################################################################################
####### Convert image to witness-generation-compatible format ##########################################################
########################################################################################################################

def process_image(image_path):
    image = _load_image(image_path)
    return _image_row_by_row_compressed(image)


def _load_image(image_path):
    log("Loading image...", end="", flush=True)
    with Image.open(image_path) as image:
        log(" Done ✅")
        return image.copy()


def _image_row_by_row_compressed(image_in):
    log("Processing image for hash computation...", end="", flush=True)
    output_array = []
    for row in np.array(image_in):
        compressed_row = []
        hex_value = ''
        for col, pixel in enumerate(row):
            if np.isscalar(pixel):  # Grayscale image
                hex_value = hex(int(pixel))[2:].zfill(6) + hex_value
            else:  # RGB image
                hex_value = ''.join(hex(int(channel))[2:].zfill(2) for channel in reversed(pixel)) + hex_value
            if (col + 1) % 10 == 0 or col == len(row) - 1:
                compressed_row.append("0x" + hex_value)
                hex_value = ''
        output_array.append(compressed_row)
    log(" Done ✅")
    return output_array


########################################################################################################################
####### Compute hash of the full image #################################################################################
########################################################################################################################

def compute_hash(image):
    accumulator = "0"  # Initial hash

    input_file = tempfile.NamedTemporaryFile("w+")
    witness_file = tempfile.NamedTemporaryFile()

    for i, row in enumerate(image):
        log(f"\rProcessing row {i + 1}/{len(image)}...", end="", flush=True)

        # Write the current row and accumulator to the input file and reset the file pointer
        json.dump({"row": row, "accumulator": accumulator}, input_file)
        input_file.seek(0)

        # Generate the witness for the current row. Read the hash from the logs.
        accumulator = subprocess.run([WITNESS_GENERATOR, input_file.name, witness_file.name],
                                     check=True, capture_output=True, text=True).stdout.strip()

    clear_current_log_line()
    log("Processed full image ✅")
    return accumulator


########################################################################################################################
####### Launch #########################################################################################################
########################################################################################################################

if __name__ == "__main__":
    prepare_witness_generator()
    image = process_image(INPUT_IMAGE)
    hash = compute_hash(image)

    log("")
    log(f"Computed hash:       {hash}")
    log(f"Computed hash (hex): {hex(int(hash))}")
