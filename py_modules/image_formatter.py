import tkinter as tk
from tkinter import filedialog
import json
from PIL import Image
import numpy as np


def get_image_path():
    root = tk.Tk()
    root.withdraw()
    file_path = filedialog.askopenfilename()
    return file_path


def compress(image_in):
    array_in = np.array(image_in).tolist()
    output_array = []
    # print(len(array_in), len(array_in[0]), len(array_in[0][0]))

    for i in range(0, len(array_in)):
        row = []
        hexValue = ''
        for j in range(0, len(array_in[i])):
            if np.isscalar(array_in[i][j]):
                hexValue = hex(int(array_in[i][j]))[2:].zfill(6) + hexValue
            else:
                for k in range(0, 3):
                    hexValue = hex(int(array_in[i][j][k]))[2:].zfill(2) + hexValue
            if j % 10 == 9:
                row.append("0x" + hexValue)
                hexValue = ''
        output_array.append(row)
    return output_array


def convert_to_grayscale(image_path):
    with Image.open(image_path) as image:
        grayscale_image = image.convert('L')
        return compress(grayscale_image)


def compress_image(image_path):
    with Image.open(image_path) as image:
        return compress(image)

# Get the image path using Tkinter file dialog
image_path = get_image_path()

if image_path:
    # Example usage
    output_path = 'formatted_image.json'  # Path to save the cropped image
    
    # Crop the image and save it
    compressed_original_image = compress_image(image_path)
    print("Image compressed successfully.")
    compressed_grayscale_image = convert_to_grayscale(image_path)
    print("Applied graysacle filter successfully.")
    out = {
        "prev_orig_hash": "0x00",
        "prev_gray_hash": "0x00",
        "row_orig": compressed_original_image[1246][:128],
        "row_gray": compressed_grayscale_image[1246][:128],
        }
    with open(output_path, 'w') as fp:
        json.dump(out, fp, indent=4)
    print("Image data dumped successfully.")
else:
    print("No image selected.")
