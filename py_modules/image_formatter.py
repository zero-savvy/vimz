import tkinter as tk
from tkinter import filedialog
import json
from PIL import Image
import numpy as np
import matplotlib.pyplot as plt
import math


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

    # Extend the array with zeros
    border_size = kernel_height // 2
    extended = [[0 for _ in range(array_width + border_size * 2)] for _ in range(array_height + border_size * 2)]
    for i in range(array_height):
        for j in range(array_width):
            extended[i+border_size][j+border_size] = array[i][j]
    
    # Initialize the output (convolved) array
    convolved_array = [[0 for _ in range(array_width)] for _ in range(array_height)]

    # Perform the convolution using nested loops
    for i in range(array_height):
        for j in range(array_width):
            conv_value = 0
            for m in range(kernel_height):
                for n in range(kernel_width):
                    conv_value += extended[i + m][j + n] * kernel[m][n]
            convolved_array[i][j] = conv_value // weight
            if convolved_array[i][j] > 255:
                convolved_array[i][j] = 255
            elif convolved_array[i][j] < 0:
                convolved_array[i][j] = 0
            # convolved_array[i][j] = extended[i][j]

    return convolved_array


def sharppen_image(image_path):
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
        plot_images_side_by_side_auto_size(np.array(image), adjusted_image)

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
        plot_images_side_by_side_auto_size(np.array(image), adjusted_image)

        return compress(adjusted_image), [["0x00"] * (len(image_np[0]) // 10)]





def convert_to_grayscale(image_path):
    with Image.open(image_path) as image:
        grayscale_image = image.convert('L')
        plot_images_side_by_side_auto_size(np.array(image), np.array(grayscale_image))
        return compress(grayscale_image)


def adjust_contrast(image_path, desired_contrast):
    with Image.open(image_path) as image:
        image_np = np.array(image)
        r_channel, g_channel, b_channel = np.rollaxis(image_np, axis=-1)
        # r_mean = int(np.mean(r_channel) *1000)
        # b_mean = int(np.mean(b_channel) *1000)
        # g_mean = int(np.mean(b_channel) *1000)
        r_mean = int(128 *1000)
        b_mean = int(128 *1000)
        g_mean = int(128 *1000)
        r_adjusted = ((r_channel - float(r_mean) / 1000) * desired_contrast + float(r_mean) / 1000).clip(0, 255).astype(np.uint8)
        g_adjusted = ((g_channel - float(g_mean) / 1000) * desired_contrast + float(g_mean) / 1000).clip(0, 255).astype(np.uint8)
        b_adjusted = ((b_channel - float(b_mean) / 1000) * desired_contrast + float(b_mean) / 1000).clip(0, 255).astype(np.uint8)
        adjusted_image = np.dstack((r_adjusted, g_adjusted, b_adjusted))
        
        plot_images_side_by_side_auto_size(image_np, adjusted_image)
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

        plot_images_side_by_side_auto_size(image_np, adjusted_image)
    
        return compress(adjusted_image)
    

def crop_image(image_path, x: int, y:int, new_width: int, new_height:int):
    with Image.open(image_path) as image:
        image_np = np.array(image)
        adjusted_image = image_np[y:y+new_height, x:x+new_width]
        # adjusted_image = [[image_np[i][j] for j in range(x, x+new_width)] for i in range(y, y+new_height)]
        plot_images_side_by_side_auto_size(image_np, adjusted_image)
    
        return compress(adjusted_image)
    

def resize_image(image_path, new_height:int, new_width: int):
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

        plot_images_side_by_side_auto_size(img_array, new_img_array)

        return compress(new_img_array)


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

        out["info"] = x * 2**24 + y * 2**12

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
        output_path = 'transformation_greyscale.json'  # Path to save the cropped image
        compressed_transformed_image = convert_to_grayscale(image_path)
        print("Applied GREYSCALE filter successfully.")

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
        out["factor"] = int(desired_contrast*10)

    elif cmd == 6:
        output_path = 'transformation_sharpen.json'  # Path to save the cropped image
        compressed_transformed_image, compressed_zeros = sharppen_image(image_path)
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
