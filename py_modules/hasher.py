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

    for i in range(0, len(array_in), 2):
        for j in range(0, len(array_in[i]), 2):
            hexValue = ''
            for k in range(0, 3):
                hexValue += '00' + hex(int(array_in[i][j][k]))[2:].zfill(2)
            for k in range(0, 3):
                hexValue += '00' + hex(int(array_in[i][j+1][k]))[2:].zfill(2)
            for k in range(0, 3):
                hexValue += '00' + hex(int(array_in[i+1][j][k]))[2:].zfill(2)
            for k in range(0, 3):
                hexValue += '00' + hex(int(array_in[i+1][j+1][k]))[2:].zfill(2)
            int(hexValue, 16)
            
    exit()

    res = {
        "original": array_in,
        "transformed": array_t,
    }
    f = open("out.json", "w")
    json.dump(res, f)


def hash_image(image_path, output_path):
    with Image.open(image_path) as image:
        compress(image)

# Get the image path using Tkinter file dialog
image_path = get_image_path()

if image_path:
    # Example usage
    output_path = 'cropped_image.jpg'  # Path to save the cropped image
    
    # Crop the image and save it
    hash_image(image_path, output_path)
    print("Image cropped and saved successfully.")
else:
    print("No image selected.")



# p = subprocess.Popen(['/usr/local/bin/node', '../js/poseidon_hasher.js', ''], stdout=subprocess.PIPE)
# out = p.stdout.read()
# print(out)