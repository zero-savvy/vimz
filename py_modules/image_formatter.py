import tkinter as tk
from tkinter import filedialog
import json
from PIL import Image
import numpy as np
import matplotlib.pyplot as plt


VESTA_PRIME = 28948022309329048855892746252171976963363056481941647379679742748393362948097


def get_image_path():
    root = tk.Tk()
    root.withdraw()
    file_path = filedialog.askopenfilename()
    return file_path


def plot_images_side_by_side_auto_size(np_image1, np_image2):
    """
    Plot two NumPy array images side by side as subfigures using matplotlib.
    Adjusts the figure size based on the dimensions of the input images.

    Args:
    np_image1 (numpy.ndarray): The first input image as a NumPy array.
    np_image2 (numpy.ndarray): The second input image as a NumPy array.
    title1 (str): The title for the first subfigure.
    title2 (str): The title for the second subfigure.

    Returns:
    None
    """
    height1, width1 = np_image1.shape[:2]
    height2, width2 = np_image2.shape[:2]

    # Calculate the total width and maximum height of the two images
    total_width = width1 + width2
    max_height = max(height1, height2)

    desired_width = 1000  # Pixels

    scaling_factor = desired_width / total_width

    plt.figure(figsize=(desired_width / 80, max_height * scaling_factor / 80))

    plt.subplot(1, 2, 1)
    plt.imshow(np_image1, cmap='gray' if len(np_image1.shape) == 2 else None)
    plt.title("Original")
    plt.axis('off')

    plt.subplot(1, 2, 2)
    plt.imshow(np_image2, cmap='gray' if len(np_image2.shape) == 2 else None)
    plt.title("Transformed")
    plt.axis('off')

    plt.show()


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


def conv2d(array, kernel, weight=1):
    # Get the dimensions of the input array and kernel
    array_height, array_width = len(array), len(array[0])
    kernel_height, kernel_width = len(kernel), len(kernel[0])

    # Calculate the output dimensions
    output_height = array_height - kernel_height + 1
    output_width = array_width - kernel_width + 1

    # Initialize the output (convolved) array
    convolved_array = [[0 for _ in range(output_width)] for _ in range(output_height)]

    # Perform the convolution using nested loops
    for i in range(output_height):
        for j in range(output_width):
            conv_value = 0
            for m in range(kernel_height):
                for n in range(kernel_width):
                    conv_value += array[i + m][j + n] * kernel[m][n]
            convolved_array[i][j] = conv_value // weight

    return convolved_array


def sharppen_image(image_path):
    kernel = np.array([
        [0, -1, 0],
        [-1,  5, -1],
        [0, -1, 0]
    ])
    with Image.open(image_path) as image:
        image_np = np.array(image)
        r_channel, g_channel, b_channel = np.rollaxis(image_np, axis=-1)
        r_adjusted = conv2d(r_channel, kernel)
        g_adjusted = conv2d(g_channel, kernel)
        b_adjusted = conv2d(b_channel, kernel)
        adjusted_image = np.dstack((r_adjusted, g_adjusted, b_adjusted))
        plot_images_side_by_side_auto_size(np.array(image), adjusted_image)
        return compress(adjusted_image)


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
        plot_images_side_by_side_auto_size(np.array(image), adjusted_image)
        return compress(adjusted_image)





def convert_to_grayscale(image_path):
    with Image.open(image_path) as image:
        grayscale_image = image.convert('L')
        plot_images_side_by_side_auto_size(np.array(image), np.array(grayscale_image))
        return compress(grayscale_image)


def adjust_contrast(image_path, desired_contrast):
    with Image.open(image_path) as image:
        image_np = np.array(image)
        r_channel, g_channel, b_channel = np.rollaxis(image_np, axis=-1)
        r_mean = int(np.mean(r_channel) *1000)
        b_mean = int(np.mean(b_channel) *1000)
        g_mean = int(np.mean(b_channel) *1000)
        r_adjusted = ((r_channel - float(r_mean) / 1000) * desired_contrast + float(r_mean) / 1000).clip(0, 255).astype(np.uint8)
        g_adjusted = ((g_channel - float(g_mean) / 1000) * desired_contrast + float(g_mean) / 1000).clip(0, 255).astype(np.uint8)
        b_adjusted = ((b_channel - float(b_mean) / 1000) * desired_contrast + float(b_mean) / 1000).clip(0, 255).astype(np.uint8)
        adjusted_image = np.dstack((r_adjusted, g_adjusted, b_adjusted))
        print('np.mean(r_channel): ', r_mean)
        print('np.mean(g_channel): ', g_mean)
        print('np.mean(b_channel): ', b_mean)
        plot_images_side_by_side_auto_size(image_np, adjusted_image)
        return r_mean, \
            g_mean, \
            b_mean, \
            compress(adjusted_image)


def compress_image(image_path):
    with Image.open(image_path) as image:
        return compress(image)
    

def adjust_brightness(np_image, brightness_factor):
    with Image.open(image_path) as image:
        image_np = np.array(image)
        np_image_float = image_np.astype(float)
        adjusted_image_float = np_image_float * brightness_factor
        adjusted_image = np.clip(adjusted_image_float, 0, 255).astype(np.uint8)

        plot_images_side_by_side_auto_size(image_np, adjusted_image)
    
        return compress(adjusted_image)
    

def crop_image(image_path, x: int, y:int, new_width: int, new_height:int):
    with Image.open(image_path) as image:
        image_np = np.array(image)
        adjusted_image = image_np[y:y+new_height, x:x+new_width]
        # adjusted_image = [[image_np[i][j] for j in range(x, x+new_width)] for i in range(y, y+new_height)]
        plot_images_side_by_side_auto_size(image_np, adjusted_image)
    
        return compress(adjusted_image)


# Get the image path using Tkinter file dialog
image_path = get_image_path()

if image_path:
    # Example usage
    
    # Crop the image and save it
    compressed_original_image = compress_image(image_path)
    out = {
        "original": compressed_original_image,
    }
    print("Image compressed successfully.")
    cmd = int(input("Enter your command (default[1]): 1) crop, 2) resize, 3) greyscale, 4) rotate, 5) flip, " 
                "6) censor, 7) change color space, 8) brightness, 9) contrast, 10) sharpen, 11) blur, "
                "12) translate: ") or "1")
    
    if cmd == 1:
        output_path = 'transformation_crop.json'  # Path to save the cropped image
        x = int(input("Enter x coordination:"))
        y = int(input("Enter y coordination:"))
        crop_size = int(input("Enter crop_size:"))
        if crop_size == 1:
            w = 640
            h = 480
        elif crop_size == 2:
            w = 1280
            h = 720
        else:
            print("The entered command was wrong. It should an Integer from 1 to 2.")
        compressed_transformed_image = crop_image(image_path, x, y, w, h)
        print("Applied CROP filter successfully.")

        out["x"] = x
        out["y"] = y

    elif cmd == 2:
        output_path = 'transformation_resize.json'  # Path to save the cropped image
        compressed_transformed_image = convert_to_grayscale(image_path)
        print("Applied RESIZE filter successfully.")

        out["transformed"] = compressed_transformed_image

    elif cmd == 3:
        output_path = 'transformation_greyscale.json'  # Path to save the cropped image
        compressed_transformed_image = convert_to_grayscale(image_path)
        print("Applied GREYSCALE filter successfully.")

        out["transformed"] = compressed_transformed_image

    elif cmd == 4:
        output_path = 'transformation_rotate.json'  # Path to save the cropped image
        compressed_transformed_image = convert_to_grayscale(image_path)
        print("Applied ROTATE filter successfully.")
        
        out["transformed"] = compressed_transformed_image

    elif cmd == 5:
        output_path = 'transformation_flip.json'  # Path to save the cropped image
        compressed_transformed_image = convert_to_grayscale(image_path)
        print("Applied FLIP filter successfully.")

        out["transformed"] = compressed_transformed_image

    elif cmd == 6:
        output_path = 'transformation_censor.json'  # Path to save the cropped image
        compressed_transformed_image = convert_to_grayscale(image_path)
        print("Applied CENSOR filter successfully.")
        
        out["transformed"] = compressed_transformed_image

    elif cmd == 7:
        output_path = 'transformation_colorchaing.json'  # Path to save the cropped image
        compressed_transformed_image = convert_to_grayscale(image_path)
        print(f"Applied {'RGB' if cmd1 == 1 else 'YCbCr'} filter successfully.")
        
        out["transformed"] = compressed_transformed_image

    elif cmd == 8:
        output_path = 'transformation_brightness.json'  # Path to save the cropped image
        desired_brightness = float(input("Enter desired brightness factor (1.00 = no effect):"))
        compressed_transformed_image = adjust_brightness(image_path, desired_brightness)
        print("Applied BRIGHTNESS filter successfully.")
        
        out["transformed"] = compressed_transformed_image
        out["factor"] = int(desired_brightness * 1000)


    elif cmd == 9:
        output_path = 'transformation_contrast.json'  # Path to save the cropped image
        desired_contrast = float(input("Enter desired contrast (1.00 = no effect):"))
        r_mean, g_mean, b_mean, compressed_transformed_image = adjust_contrast(image_path, desired_contrast)
        print("Applied CONTRAST filter successfully.")
        
        out["transformed"] = compressed_transformed_image
        out["r_mean"] = r_mean
        out["g_mean"] = g_mean
        out["b_mean"] = b_mean
        out["factor"] = int(desired_contrast*1000)

    elif cmd == 10:
        output_path = 'transformation_sharpen.json'  # Path to save the cropped image
        compressed_transformed_image = sharppen_image(image_path)
        print("Applied SHARPNESS filter successfully.")
        
        out["transformed"] = compressed_transformed_image

    elif cmd == 11:
        output_path = 'transformation_blur.json'  # Path to save the cropped image
        compressed_transformed_image = blur_image(image_path)
        print("Applied BLUR filter successfully.")
        
        out["transformed"] = compressed_transformed_image

    elif cmd == 12:
        output_path = 'transformation_translate.json'  # Path to save the cropped image
        compressed_transformed_image = convert_to_grayscale(image_path)
        print("Applied TRANSLATE filter successfully.")
        
        out["transformed"] = compressed_transformed_image

    else:
        print("The entered command was wrong. It should an Integer from 1 to 12.")
        exit()
    
    with open(output_path, 'w') as fp:
        json.dump(out, fp, indent=4)
    print("Image data dumped successfully.")
else:
    print("No image selected.")
