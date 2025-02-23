import json
import subprocess
import sys
import tempfile
from os import path

import numpy as np
from PIL import Image

from pyvimz.img.ops import compress

########################################################################################################################
####### Environment ####################################################################################################
########################################################################################################################

CIRCUIT_DIR = "./circuits"
CIRCUIT_FILE = f"{CIRCUIT_DIR}/image_running_hash.circom"
CPP_DIR = f"{CIRCUIT_DIR}/image_running_hash_cpp"
WITNESS_GENERATOR = f"{CPP_DIR}/image_running_hash"


def log(message, **kwargs):
    """Prints a formatted log message."""
    print(f"\033[1m{message}\033[0m", **kwargs)


def clear_current_log_line():
    """Clears the current line in the terminal (for progress updates)."""
    print("\r\033[K", end="")


########################################################################################################################
####### Compile the Circom circuit and build the C++ witness generator #################################################
########################################################################################################################

def prepare_witness_generator():
    """Compiles the Circom circuit and builds the C++ witness generator if it doesn't already exist."""
    if path.exists(WITNESS_GENERATOR):
        log(f"Witness generator already exists at {WITNESS_GENERATOR}.")
    else:
        _compile_circuit()
        _build_witness_generator()


def _compile_circuit():
    """Compiles the Circom circuit."""
    log("Compiling Circom circuit...", end="", flush=True)
    subprocess.run(["circom", CIRCUIT_FILE, "--O2", "-c", "-o", CIRCUIT_DIR], check=True, stdout=subprocess.DEVNULL)
    log(" Done ✅")


def _build_witness_generator():
    """Builds the C++ witness generator using Make."""
    log("Building C++ witness generator...", end="", flush=True)
    subprocess.run(["make", "-C", CPP_DIR], check=True, stdout=subprocess.DEVNULL)
    log(" Done ✅")


########################################################################################################################
####### Convert image to witness-generation-compatible format ##########################################################
########################################################################################################################

def process_image(image_path):
    """Loads an image and converts it into a compressed row-by-row format suitable for witness generation."""
    image = _load_image(image_path)
    return _compress_image(image)


def _load_image(image_path):
    """Loads an image from file."""
    log("Loading image...", end="", flush=True)
    with Image.open(image_path) as image:
        log(" Done ✅")
        return np.array(image)


def _compress_image(image):
    """Processes image row-by-row and compresses pixel data into hex format."""
    log("Processing image for hash computation...", end="", flush=True)
    result = compress(image)
    log(" Done ✅")
    return result


########################################################################################################################
####### Compute hash of the full image #################################################################################
########################################################################################################################

def compute_hash(image):
    """Computes the running hash for an image row-by-row using the Circom witness generator."""
    accumulator = "0"  # Initial hash

    with tempfile.NamedTemporaryFile("w+", delete=True) as input_file, \
            tempfile.NamedTemporaryFile(delete=True) as witness_file:
        for i, row in enumerate(image):
            log(f"\rProcessing row {i + 1}/{len(image)}...", end="", flush=True)

            # Write the current row and accumulator to the input file
            json.dump({"row": row, "accumulator": accumulator}, input_file)
            input_file.seek(0)

            # Generate the witness and read output hash
            result = subprocess.run(
                [WITNESS_GENERATOR, input_file.name, witness_file.name],
                check=True, capture_output=True, text=True
            )
            accumulator = result.stdout.strip()

        clear_current_log_line()
        log("Processed full image ✅")
        return accumulator


########################################################################################################################
####### Launch #########################################################################################################
########################################################################################################################

def main():
    if len(sys.argv) != 2:
        log("Usage: python3 main.py <image_path>")
        sys.exit(1)
    image_path = sys.argv[1]

    try:
        prepare_witness_generator()
        image_data = process_image(image_path)
        final_hash = compute_hash(image_data)

        log("")
        log(f"Computed hash:       {final_hash}")
        log(f"Computed hash (hex): {hex(int(final_hash))}")

    except Exception as e:
        log(f"❌ Error: {e}")
