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


def beauty_output(image_in, image_t):
    array_in = np.array(image_in)
    array_t = np.array(image_t)

    res = {
        "original": array_in.tolist(),
        "transformed": array_t.tolist(),
    }
    f = open("out.json", "w")
    json.dump(res, f)


def crop_and_save_image(image_path, output_path, crop_box):
    with Image.open(image_path) as image:
        cropped_image = image.crop(crop_box)
        cropped_image.save(output_path)
        beauty_output(image, cropped_image)

# Get the image path using Tkinter file dialog
image_path = get_image_path()

if image_path:
    # Example usage
    output_path = 'cropped_image.jpg'  # Path to save the cropped image
    crop_box = (100, 100, 400, 400)  # Specify the crop box as (left, upper, right, lower)

    # Crop the image and save it
    crop_and_save_image(image_path, output_path, crop_box)
    print("Image cropped and saved successfully.")
else:
    print("No image selected.")
