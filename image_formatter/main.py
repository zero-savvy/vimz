import argparse
import json
import tkinter as tk
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


def compress_image(image_path):
    with Image.open(image_path) as image:
        return compress(image)


def adjust_brightness(np_image, brightness_factor):
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


def get_image_path():
    """Get the image path from the command line arguments or using a file dialog."""

    # Try to get the image path from the command line arguments.
    parser = argparse.ArgumentParser(description="Image sharpening tool.")
    parser.add_argument(
        "image_path",
        default=None,
        nargs="?",
        help="Path to the input image. If not provided, an interactive file dialog will open."
    )
    args = parser.parse_args()
    if args.image_path is not None:
        return args.image_path

    # If the image path is not provided as an argument, open a file dialog.
    print("No image path provided. Please select an image file.")
    tk.Tk().withdraw()
    return filedialog.askopenfilename(
        title="Select an Image",
        filetypes=[("Image files", ["*.jpg","*.jpeg","*.png","*.bmp","*.tiff"])]
    )


image_path = get_image_path()

if image_path:
    # Example usage

    # Crop the image and save it
    compressed_original_image = compress_image(image_path)
    out = {
        "original": compressed_original_image,
    }
    print("Image compressed successfully.")
    cmd = int(input("Enter your command (default[1]): 1) crop, 2) resize, 3) greyscale, 4) brightness,"
                    " 5) contrast, 6) sharpen, 7) blur: ") or "1")

    if cmd == 1:
        output_path = 'transformation_crop.json'  # Path to save the cropped image
        x = int(input("Enter x coordination:"))
        y = int(input("Enter y coordination:"))
        crop_size = int(input("Enter crop_size: 1) SD, 2) HD, 3) FHD: "))
        if crop_size == 1:
            w = 640
            h = 480
        elif crop_size == 2:
            w = 1280
            h = 720
        elif crop_size == 3:
            w = 1920
            h = 1080
        else:
            print("The entered command was wrong. It should an Integer from 1 to 3.")
            exit()
        compressed_transformed_image = crop_image(image_path, x, y, w, h)
        print("Applied CROP filter successfully.")

        out["info"] = x * 2 ** 24 + y * 2 ** 12

    elif cmd == 2:
        output_path = 'transformation_resize.json'  # Path to save the resized image
        new_size = int(input("Enter resize: 1) HD --> SD, 2) 4K --> FHD: "))
        if new_size == 1:
            w = 640
            h = 480
        elif new_size == 2:
            w = 1920
            h = 1080
        else:
            print("The entered command was wrong. It should an Integer from 1 to 2.")
        compressed_transformed_image = resize_image(image_path, h, w)
        print("Applied RESIZE filter successfully.")

        out["transformed"] = compressed_transformed_image

    elif cmd == 3:
        output_path = 'transformation_grayscale.json'  # Path to save the cropped image
        compressed_transformed_image = convert_to_grayscale(image_path)
        print("Applied GRAYSCALE filter successfully.")

        out["transformed"] = compressed_transformed_image


    elif cmd == 4:
        output_path = 'transformation_brightness.json'  # Path to save the cropped image
        desired_brightness = float(input("Enter desired brightness factor (1.00 = no effect):"))
        compressed_transformed_image = adjust_brightness(image_path, desired_brightness)
        print("Applied BRIGHTNESS filter successfully.")

        out["transformed"] = compressed_transformed_image
        out["factor"] = int(desired_brightness * 10)


    elif cmd == 5:
        output_path = 'transformation_contrast.json'  # Path to save the cropped image
        desired_contrast = float(input("Enter desired contrast (1.00 = no effect):"))
        compressed_transformed_image = adjust_contrast(image_path, desired_contrast)
        print("Applied CONTRAST filter successfully.")

        out["transformed"] = compressed_transformed_image
        out["factor"] = int(desired_contrast * 10)

    elif cmd == 6:
        output_path = 'transformation_sharpen.json'  # Path to save the cropped image
        compressed_transformed_image, compressed_zeros = sharpen_image(image_path)
        print("Applied SHARPNESS filter successfully.")

        out["transformed"] = compressed_transformed_image
        out["original"] = compressed_zeros + out["original"] + compressed_zeros

    elif cmd == 7:
        output_path = 'transformation_blur.json'  # Path to save the cropped image
        compressed_transformed_image, compressed_zeros = blur_image(image_path)
        print("Applied BLUR filter successfully.")

        out["transformed"] = compressed_transformed_image
        out["original"] = compressed_zeros + out["original"] + compressed_zeros

    else:
        print("The entered command was wrong. It should an Integer from 1 to 7.")
        exit()

    with open(output_path, 'w') as fp:
        json.dump(out, fp, indent=4)
    print("Image data dumped successfully.")
else:
    print("No image selected.")
