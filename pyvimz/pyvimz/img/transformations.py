import numpy as np

from pyvimz.img.ops import conv2d


def sharpen_image(image):
    kernel = np.array([
        [0, -1, 0],
        [-1, 5, -1],
        [0, -1, 0]
    ])

    image_np = np.array(image)
    r_channel, g_channel, b_channel = np.rollaxis(image_np, axis=-1)
    r_adjusted = conv2d(r_channel, kernel)
    g_adjusted = conv2d(g_channel, kernel)
    b_adjusted = conv2d(b_channel, kernel)
    adjusted_image = np.dstack((r_adjusted, g_adjusted, b_adjusted))

    return adjusted_image, [["0x00"] * (len(image_np[0]) // 10)]


def blur_image(image):
    kernel = np.array([
        [1, 1, 1],
        [1, 1, 1],
        [1, 1, 1]
    ])
    image_np = np.array(image)
    r_channel, g_channel, b_channel = np.rollaxis(image_np, axis=-1)

    r_adjusted = conv2d(r_channel, kernel, 9)
    g_adjusted = conv2d(g_channel, kernel, 9)
    b_adjusted = conv2d(b_channel, kernel, 9)
    adjusted_image = np.dstack((r_adjusted, g_adjusted, b_adjusted))

    return adjusted_image, [["0x00"] * (len(image_np[0]) // 10)]


def convert_to_grayscale(image):
    return np.array(image.convert('L'))


def adjust_contrast(image, desired_contrast):
    image_np = np.array(image)
    r_channel, g_channel, b_channel = np.rollaxis(image_np, axis=-1)
    r_mean = int(128 * 1000)
    b_mean = int(128 * 1000)
    g_mean = int(128 * 1000)
    r_adjusted = ((r_channel - float(r_mean) / 1000) * desired_contrast + float(r_mean) / 1000).clip(0, 255).astype(
        np.uint8)
    g_adjusted = ((g_channel - float(g_mean) / 1000) * desired_contrast + float(g_mean) / 1000).clip(0, 255).astype(
        np.uint8)
    b_adjusted = ((b_channel - float(b_mean) / 1000) * desired_contrast + float(b_mean) / 1000).clip(0, 255).astype(
        np.uint8)
    return np.dstack((r_adjusted, g_adjusted, b_adjusted))


def adjust_brightness(image, brightness_factor):
    image_np = np.array(image)
    np_image_float = image_np.astype(float)
    adjusted_image_float = np_image_float * brightness_factor
    return np.clip(adjusted_image_float, 0, 255).astype(np.uint8)


def crop_image(image, x: int, y: int, new_width: int, new_height: int):
    image_np = np.array(image)
    return image_np[y:y + new_height, x:x + new_width]


def random_image_redaction(image):
    image = np.array(image)
    height, width = image.shape[:2]
    block_size = 40

    # Number of blocks vertically and horizontally
    num_blocks_y = height // block_size
    num_blocks_x = width // block_size

    indicators = []
    transformed = image.copy()

    for by in range(num_blocks_y):
        for bx in range(num_blocks_x):
            # Checkerboard pattern: redact if (row + col) is odd
            redact = (by + bx) % 2 == 1
            indicators.append("0x1" if redact else "0x0")

            if redact:
                y0 = by * block_size
                x0 = bx * block_size
                transformed[y0:y0 + block_size, x0:x0 + block_size] = 0  # Zero out

    return transformed, indicators


def resize_image(image, new_height: int, new_width: int):
    img_array = np.array(image)

    # Get the dimensions of the original image
    height, width, channels = img_array.shape

    # Calculate the scaling factors for each dimension
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

    return new_img_array
