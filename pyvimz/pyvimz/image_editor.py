import argparse
import json
import tkinter as tk
from os import path
from tkinter import filedialog

from PIL import Image

from pyvimz.img.ops import compress
from pyvimz.img.transformations import *
from pyvimz.plotting import plot_images_side_by_side


def get_image_path(args):
    """Get the image path from the command line arguments or using a file dialog."""

    # Try to get the image path from the command line arguments.
    if args.image_path is not None:
        return args.image_path

    # If the image path is not provided as an argument, open a file dialog.
    print("No image path provided. Please select an image file.")
    tk.Tk().withdraw()
    return filedialog.askopenfilename(
        title="Select an Image",
        filetypes=[("Image files", ["*.jpg", "*.jpeg", "*.png", "*.bmp", "*.tiff"])]
    )


operations = {
    "blur": blur_image,
    "brightness": adjust_brightness,
    "contrast": adjust_contrast,
    "crop": crop_image,
    "grayscale": convert_to_grayscale,
    "hash": None,
    "resize": resize_image,
    "sharpness": sharpen_image,
}


def parse_args():
    parser = argparse.ArgumentParser(description="Image formatting tool")
    parser.add_argument("operation", type=str, choices=operations.keys(), help="Operation to perform on the image")

    # ====================================== FILE PATHS ======================================
    parser.add_argument(
        "--image-path", "-i",
        default=None, help="Path to the input image. If not provided, an interactive file dialog will open."
    )
    parser.add_argument("--output-dir", "-o", default="./",
                        help="Directory to save the output image. Default is the current directory.")

    # ====================================== RENDERING ======================================
    parser.add_argument("--render", action="store_true", help="Render the result")

    # ===================================== TRANSFORMATION PARAMETERS ======================================
    parser.add_argument("--factor", type=float, help="Transformation factor (for brightness and contrast operations)")

    parser.add_argument("--x", type=int, help="X coordinate for cropping")
    parser.add_argument("--y", type=int, help="Y coordinate for cropping")
    parser.add_argument("--crop-size", choices=["SD", "HD", "FHD"], help="Size of the cropped image")

    parser.add_argument("--resize-option", choices=["HD to SD", "4K to FHD"], help="Resize option")

    return parser.parse_args()


def main():
    args = parse_args()
    image_path = get_image_path(args)
    operation = args.operation

    with Image.open(image_path) as image:
        original_image = image.copy()

    # Initialize the output dictionary
    out = {"original": compress(original_image)}

    with Image.open(image_path) as image:
        workspace_image = image.copy()

    if operation == "hash":
        # nothing to do here for now (currently, we don't check public input)
        transformed = None

    elif operation == "grayscale":
        transformed = operations[operation](workspace_image)

    elif operation in {"brightness", "contrast"}:
        factor = args.factor
        transformed = operations[operation](workspace_image, factor)
        out["factor"] = int(factor * 10)

    elif operation in {"sharpness", "blur"}:
        transformed_image, zeros = operations[operation](workspace_image)
        # Extend the original image with zero-padding
        out["original"] = zeros + compress(original_image) + zeros
        transformed = transformed_image

    elif operation == "crop":
        x, y, crop_size = args.x, args.y, args.crop_size

        size_map = {"sd": (640, 480), "hd": (1280, 720), "fhd": (1920, 1080)}
        w, h = size_map[crop_size.lower()]

        transformed = operations[operation](workspace_image, x, y, w, h)
        out["info"] = x * 2 ** 24 + y * 2 ** 12

    elif operation == "resize":
        resize_option = args.resize_option.lower()
        size_map = {"hd to sd": (640, 480), "4k to fhd": (1920, 1080)}

        if resize_option in size_map:
            w, h = size_map[resize_option]
            transformed = operations[operation](workspace_image, h, w)
        else:
            raise Exception("Invalid resize option.")

    if transformed is not None:
        out["transformed"] = compress(transformed)
        if args.render:
            plot_images_side_by_side(np.array(original_image), transformed)

    # Save the output to a JSON file
    output_path = path.join(args.output_dir, f"{operation}.json")
    with open(output_path, "w") as fp:
        json.dump(out, fp, indent=4)
    print(f"Transformation {operation} applied successfully. Data saved to {output_path}.")
