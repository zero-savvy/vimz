import tkinter as tk
from tkinter import filedialog
from PIL import Image

def get_image_path():
    root = tk.Tk()
    root.withdraw()
    file_path = filedialog.askopenfilename()
    return file_path

def resize_and_save_image(input_path, output_path, size):
    with Image.open(input_path) as image:
        resized_image = image.resize(size, Image.BILINEAR)
        resized_image.save(output_path)

# Get the image path using Tkinter file dialog
image_path = get_image_path()

if image_path:
    # Example usage
    new_size = (800, 600)  # New size for the image (width, height)
    output_path = 'resized_image.jpg'  # Path to save the resized image

    # Resize and save the image
    resize_and_save_image(image_path, output_path, new_size)
    print("Image resized and saved successfully.")
else:
    print("No image selected.")
