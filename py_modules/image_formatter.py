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
    cmd = input("Enter your command (default[1]): 1) crop, 2) resize, 3) greyscale, 4) rotate, 5) flip, " 
                "6) censor, 7) change color space, 8) white balance, 9) contrast, 10) sharpen, 11) blur, "
                "12) translate")
    if cmd == 1:
        compressed_transformed_image = convert_to_grayscale(image_path)
        print("Applied CROP filter successfully.")
    elif cmd == 2:
        compressed_transformed_image = convert_to_grayscale(image_path)
        print("Applied RESIZE filter successfully.")
    elif cmd == 3:
        compressed_transformed_image = convert_to_grayscale(image_path)
        print("Applied GREYSCALE filter successfully.")
    elif cmd == 4:
        compressed_transformed_image = convert_to_grayscale(image_path)
        print("Applied ROTATE filter successfully.")
    elif cmd == 5:
        compressed_transformed_image = convert_to_grayscale(image_path)
        print("Applied FLIP filter successfully.")
    elif cmd == 6:
        compressed_transformed_image = convert_to_grayscale(image_path)
        print("Applied CENSOR filter successfully.")
    elif cmd == 7:
        compressed_transformed_image = convert_to_grayscale(image_path)
        print(f"Applied {'RGB' if cmd1 == 1 else 'YCbCr'} filter successfully.")
    elif cmd == 8:
        compressed_transformed_image = convert_to_grayscale(image_path)
        print("Applied WHITE BALANCE filter successfully.")
    elif cmd == 9:
        compressed_transformed_image = convert_to_grayscale(image_path)
        print("Applied graysacle filter successfully.")
    elif cmd == 10:
        compressed_transformed_image = convert_to_grayscale(image_path)
        print("Applied graysacle filter successfully.")
    elif cmd == 11:
        compressed_transformed_image = convert_to_grayscale(image_path)
        print("Applied graysacle filter successfully.")
    elif cmd == 12:
        compressed_transformed_image = convert_to_grayscale(image_path)
        print("Applied graysacle filter successfully.")
    out = {
        "original": compressed_original_image,
        "transformed": compressed_transformed_image,
        }
    with open(output_path, 'w') as fp:
        json.dump(out, fp, indent=4)
    print("Image data dumped successfully.")
else:
    print("No image selected.")
