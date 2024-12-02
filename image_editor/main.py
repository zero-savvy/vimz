import argparse
import json
import tkinter as tk
from os import path
from tkinter import filedialog

import numpy as np
from PIL import Image

from img_utils import compress, conv2d
from plotting import plot_images_side_by_side


def sharpen_image(image_path):
    kernel = np.array([
        [0, -1, 0],
        [-1, 5, -1],
        [0, -1, 0]
    ])
    with Image.open(image_path) as image:
        image_np = np.array(image)
        r_channel, g_channel, b_channel = np.rollaxis(image_np, axis=-1)
        r_adjusted = conv2d(r_channel, kernel)
        g_adjusted = conv2d(g_channel, kernel)
        b_adjusted = conv2d(b_channel, kernel)
        adjusted_image = np.dstack((r_adjusted, g_adjusted, b_adjusted))
        plot_images_side_by_side(np.array(image), adjusted_image)

        return compress(adjusted_image), [["0x00"] * (len(image_np[0]) // 10)]


def blur_image(image_path):
    kernel = np.array([
        [1, 1, 1],
        [1, 1, 1],
        [1, 1, 1]
    ])
    with Image.open(image_path) as image:
        image_np = np.array(image)
        r_channel, g_channel, b_channel = np.rollaxis(image_np, axis=-1)

        r_adjusted = conv2d(r_channel, kernel, 9)
        g_adjusted = conv2d(g_channel, kernel, 9)
        b_adjusted = conv2d(b_channel, kernel, 9)
        adjusted_image = np.dstack((r_adjusted, g_adjusted, b_adjusted))
        plot_images_side_by_side(np.array(image), adjusted_image)

        return compress(adjusted_image), [["0x00"] * (len(image_np[0]) // 10)]


def convert_to_grayscale(image_path):
    with Image.open(image_path) as image:
        grayscale_image = image.convert('L')
        plot_images_side_by_side(np.array(image), np.array(grayscale_image))
        return compress(grayscale_image)


def adjust_contrast(image_path, desired_contrast):
    with Image.open(image_path) as image:
        image_np = np.array(image)
        r_channel, g_channel, b_channel = np.rollaxis(image_np, axis=-1)
        # r_mean = int(np.mean(r_channel) *1000)
        # b_mean = int(np.mean(b_channel) *1000)
        # g_mean = int(np.mean(b_channel) *1000)
        r_mean = int(128 * 1000)
        b_mean = int(128 * 1000)
        g_mean = int(128 * 1000)
        r_adjusted = ((r_channel - float(r_mean) / 1000) * desired_contrast + float(r_mean) / 1000).clip(0, 255).astype(
            np.uint8)
        g_adjusted = ((g_channel - float(g_mean) / 1000) * desired_contrast + float(g_mean) / 1000).clip(0, 255).astype(
            np.uint8)
        b_adjusted = ((b_channel - float(b_mean) / 1000) * desired_contrast + float(b_mean) / 1000).clip(0, 255).astype(
            np.uint8)
        adjusted_image = np.dstack((r_adjusted, g_adjusted, b_adjusted))

        plot_images_side_by_side(image_np, adjusted_image)
        return compress(adjusted_image)


def adjust_brightness(image_path, brightness_factor):
    with Image.open(image_path) as image:
        image_np = np.array(image)
        np_image_float = image_np.astype(float)
        adjusted_image_float = np_image_float * brightness_factor
        adjusted_image = np.clip(adjusted_image_float, 0, 255).astype(np.uint8)

        plot_images_side_by_side(image_np, adjusted_image)

        return compress(adjusted_image)


def crop_image(image_path, x: int, y: int, new_width: int, new_height: int):
    with Image.open(image_path) as image:
        image_np = np.array(image)
        adjusted_image = image_np[y:y + new_height, x:x + new_width]
        # adjusted_image = [[image_np[i][j] for j in range(x, x+new_width)] for i in range(y, y+new_height)]
        plot_images_side_by_side(image_np, adjusted_image)

        return compress(adjusted_image)


def resize_image(image_path, new_height: int, new_width: int):
    with Image.open(image_path) as image:
        # image_np = np.array(image)
        # adjusted_image = image.resize((new_width, new_height), resample=Image.Resampling.BILINEAR)
        # adjusted_image_np = np.array(adjusted_image)

        # adjusted_image = [[image_np[i][j] for j in range(x, x+new_width)] for i in range(y, y+new_height)]

        img_array = np.array(image)

        # Get the dimensions of the original image
        height, width, channels = img_array.shape

        # Calculate the scaling factors for each dimension
        # scale_y = (new_height - 1) / (height - 1)
        # scale_x = (new_width - 1) / (width - 1)

        x_ratio = float(width) / float(new_width)
        y_ratio = float(height) / float(new_height)

        # Initialize the new image array
        new_img_array = np.zeros((new_height, new_width, channels), dtype=np.uint8)

        if height == 720:
            # Perform bilinear interpolation
            for i in range(new_height):
                for j in range(new_width):
                    x_l = int(j * x_ratio)
                    x_h = int(j * x_ratio) + 1
                    y_l = int(i * y_ratio)
                    y_h = int(i * y_ratio) + 1

                    a = img_array[y_l, x_l]
                    b = img_array[y_l, x_h]
                    c = img_array[y_h, x_l]
                    d = img_array[y_h, x_h]

                    weight = 2 if i % 2 == 0 else 1
                    weight = float(weight) / 3
                    summ = a * weight + b * weight \
                           + c * (1 - weight) + d * (1 - weight)
                    new_img_array[i, j] = summ / 2
        else:
            # Perform bilinear interpolation
            for i in range(new_height):
                for j in range(new_width):
                    x_l = int(j * x_ratio)
                    x_h = int(j * x_ratio) + 1
                    y_l = int(i * y_ratio)
                    y_h = int(i * y_ratio) + 1

                    a = img_array[y_l, x_l]
                    b = img_array[y_l, x_h]
                    c = img_array[y_h, x_l]
                    d = img_array[y_h, x_h]

                    weight = float(1) / 2
                    summ = a * weight + b * weight + c * weight + d * weight
                    new_img_array[i, j] = summ / 2

        plot_images_side_by_side(img_array, new_img_array)

        return compress(new_img_array)


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
    "crop": crop_image,
    "resize": resize_image,
    "grayscale": convert_to_grayscale,
    "brightness": adjust_brightness,
    "contrast": adjust_contrast,
    "sharpen": sharpen_image,
    "blur": blur_image,
}


def parse_args():
    parser = argparse.ArgumentParser(description="Image formatting tool")
    parser.add_argument(
        "operation",
        type=str,
        choices=operations.keys(),
        help="Operation to perform on the image"
    )
    parser.add_argument(
        "--image_path",
        default=None,
        help="Path to the input image. If not provided, an interactive file dialog will open."
    )
    parser.add_argument(
        "--output_dir",
        default="./",
        help="Directory to save the output image. Default is the current directory."
    )
    return parser.parse_args()


def main():
    args = parse_args()
    image_path = get_image_path(args)
    operation = args.operation

    # Compress and serialize the original image
    with Image.open(image_path) as image:
        original_image = compress(image)
    out = {"original": original_image}
    print(f"Image compressed successfully. Selected operation: {operation}")

    if operation == "crop":
        x = int(input("Enter x coordinate: "))
        y = int(input("Enter y coordinate: "))
        crop_size = input("Enter crop size (SD, HD, FHD): ").lower()
        size_map = {"sd": (640, 480), "hd": (1280, 720), "fhd": (1920, 1080)}

        if crop_size in size_map:
            w, h = size_map[crop_size]
            out["transformed"] = operations[operation](image_path, x, y, w, h)
            out["info"] = x * 2 ** 24 + y * 2 ** 12
        else:
            print("Invalid crop size. Use SD, HD, or FHD.")
            return

    elif operation == "resize":
        resize_option = input("Enter resize option (HD to SD, 4K to FHD): ").lower()
        size_map = {"hd to sd": (640, 480), "4k to fhd": (1920, 1080)}

        if resize_option in size_map:
            w, h = size_map[resize_option]
            out["transformed"] = operations[operation](image_path, h, w)
        else:
            print("Invalid resize option.")
            return

    elif operation in {"brightness", "contrast"}:
        factor = float(input(f"Enter {operation} factor (1.00 = no effect): "))
        out["transformed"] = operations[operation](image_path, factor)
        out["factor"] = int(factor * 10)

    elif operation == "grayscale":
        out["transformed"] = operations[operation](image_path)

    elif operation in {"sharpen", "blur"}:
        transformed_image, zeros = operations[operation](image_path)
        out["original"] = zeros + original_image + zeros
        out["transformed"] = transformed_image

    else:
        print(f"Operation '{operation}' is not implemented.")
        return

    output_path = path.join(args.output_dir, f"transformation_{operation}.json")

    # Save the output to a JSON file
    with open(output_path, "w") as fp:
        json.dump(out, fp, indent=4)
    print(f"Transformation data saved to {output_path}.")


if __name__ == "__main__":
    main()
