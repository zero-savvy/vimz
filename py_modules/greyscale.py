import tkinter as tk
from tkinter import filedialog
from PIL import Image

def get_image_path():
    root = tk.Tk()
    root.withdraw()
    file_path = filedialog.askopenfilename()
    return file_path

def convert_to_grayscale(image_path, output_path):
    with Image.open(image_path) as image:
        grayscale_image = image.convert('L')
        grayscale_image.save(output_path)

# Get the image path using Tkinter file dialog
image_path = get_image_path()

if image_path:
    # Example usage
    output_path = 'grayscale_image.jpg'  # Path to save the grayscale image

    # Convert the image to grayscale and save it
    convert_to_grayscale(image_path, output_path)
    print("Image converted to grayscale and saved successfully.")
else:
    print("No image selected.")
