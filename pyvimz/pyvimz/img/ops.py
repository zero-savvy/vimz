import numpy as np


def compress_by_rows(image):
    """
    Compress an image array, row by row, by packing batches of 10 pixels into field elements
    (represented as hexadecimal strings).

    Args:
        image (array-like): The input image, typically a 2D (grayscale) or 3D (RGB) array.

    Returns:
        A 2D list of hexadecimal strings representing chunks of the image.
    """
    output = []

    for row in np.array(image):
        compressed_row = []
        hex_value = ''
        for col, pixel in enumerate(row):
            if np.isscalar(pixel):  # Grayscale image
                hex_value = hex(int(pixel))[2:].zfill(6) + hex_value
            else:  # RGB image
                hex_value = ''.join(hex(int(channel))[2:].zfill(2) for channel in reversed(pixel)) + hex_value

            # Append every 10 pixels as a single chunk. If the row ends, append the remaining pixels.
            if (col + 1) % 10 == 0 or col == len(row) - 1:
                compressed_row.append("0x" + hex_value)
                hex_value = ''

        output.append(compressed_row)

    return output


def compress_by_blocks(image):
    """
    Compress an image by iterating over 40x40 blocks, compressing pixels into hex strings.

    Args:
        image (array-like): The input image, typically a 2D (grayscale) or 3D (RGB) array.

    Returns:
        A 2D list where each sublist corresponds to a 40x40 block compressed into 160 hex strings.
    """
    image = np.array(image)
    h, w = image.shape[:2]
    output = []

    for block_row in range(0, h, 40):
        for block_col in range(0, w, 40):
            compressed_block = []
            for row in range(block_row, min(block_row + 40, h)):  # Process row within the block
                hex_value = ''
                for col in range(block_col, min(block_col + 40, w)):  # Process column within the block
                    pixel = image[row, col]

                    if np.isscalar(pixel):  # Grayscale image
                        hex_value = hex(int(pixel))[2:].zfill(6) + hex_value
                    else:  # RGB image
                        hex_value = ''.join(hex(int(channel))[2:].zfill(2) for channel in reversed(pixel)) + hex_value

                    # Append every 10 pixels as a single chunk
                    if (col - block_col + 1) % 10 == 0 or col == min(block_col + 40, w) - 1:
                        compressed_block.append("0x" + hex_value)
                        hex_value = ''

            output.append(compressed_block)  # Each block results in 160 hex values

    return output


def conv2d(array: np.ndarray, kernel: np.ndarray, weight: int = 1) -> np.ndarray:
    """
    Perform 2D convolution on a NumPy array (grayscale image) with a given kernel.

    Args:
        array (np.ndarray): 2D input array (grayscale image).
        kernel (np.ndarray): 2D kernel array.
        weight (int): Normalization weight to divide the convolution result. Defaults to 1.

    Returns:
        np.ndarray: The convolved 2D array.
    """
    if array.ndim != 2:
        raise ValueError("Input array must be a 2D array.")
    if kernel.ndim != 2:
        raise ValueError("Kernel must be a 2D array.")

    array_height, array_width = array.shape
    kernel_height, kernel_width = kernel.shape

    # Add zero padding to the input array
    pad_h, pad_w = kernel_height // 2, kernel_width // 2
    padded_array = np.pad(array, ((pad_h, pad_h), (pad_w, pad_w)), mode='constant', constant_values=0)

    # Perform convolution
    convolved_array = np.zeros((array_height, array_width), dtype=np.int32)
    for i in range(array_height):
        for j in range(array_width):
            sub_array = padded_array[i:i + kernel_height, j:j + kernel_width]
            conv_value = np.sum(sub_array * kernel)
            convolved_array[i, j] = max(0, min(255, conv_value // weight))  # Clamp to [0, 255]

    return convolved_array.astype(np.uint8)
