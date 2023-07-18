import tkinter as tk
from tkinter import filedialog
from PIL import Image

def get_image_path():
    root = tk.Tk()
    root.withdraw()
    file_path = filedialog.askopenfilename()
    return file_path

def crop_and_save_image(image_path, output_path, crop_box):
    with Image.open(image_path) as image:
        cropped_image = image.crop(crop_box)
        cropped_image.save(output_path)

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
