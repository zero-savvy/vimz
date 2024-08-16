import tkinter as tk
from tkinter import filedialog
from PIL import Image, ImageTk, ImageDraw
import numpy as np
import json

def compress_image(image_path):
    with Image.open(image_path) as image:
        return compress(image)

def compress(image_in):
    array_in = np.array(image_in)
    rows, cols = array_in.shape[:2]
    output_array = []
    block_size = 10
    for i in range(0, rows, block_size):
        for j in range(0, cols, block_size):
            block = []
            hexValue = ''
            counter = 0
            # for on each block
            for k in range(block_size):
                for l in range (block_size):
                    if i + k < rows and j + l < cols:  # Ensure we're within the image boundaries
                        pixel = array_in[i + k, j + l]
                        if np.isscalar(pixel):
                            hexValue = hex(int(pixel))[2:].zfill(6) + hexValue
                        else:
                            for m in range(3):  # Process RGB values
                                hexValue = hex(int(pixel[m]))[2:].zfill(2) + hexValue
                        counter += 1
                        if counter % 10 == 0:
                            block.append("0x" + hexValue)
                            hexValue = ''
                            counter = 0
            output_array.append(block)
    return output_array

def get_image_path():
    root = tk.Tk()
    root.withdraw()
    file_path = filedialog.askopenfilename()
    return file_path

def load_image(image_path):
    try:
        return Image.open(image_path)
    except Exception as e:
        print(f"Error loading image: {e}")
        return None

def redact_image(image, block_size, selected_blocks):
    # Create a draw object to modify the image
    draw = ImageDraw.Draw(image)
    for block_x, block_y in selected_blocks:
        x1 = block_x * block_size
        y1 = block_y * block_size
        x2 = x1 + block_size
        y2 = y1 + block_size
        draw.rectangle([x1, y1, x2, y2], fill="black")
    return image

def save_image(image, path):
    image.save(path)

def on_click(event, canvas, grid_size, image, block_size, selected_blocks, redacted_mask):
    # Calculate the block position
    block_x = event.x // block_size
    block_y = event.y // block_size
    block_position = (block_x, block_y)
    index = block_y * grid_size[0] + block_x

    if block_position in selected_blocks:
        # If the block is already selected, deselect it
        selected_blocks.remove(block_position)
        redacted_mask[index] = 0  # Mark this block as not redacted
        # redraw_canvas(canvas, image, grid_size, block_size, selected_blocks)
    else:
        # If the block is not selected, select it
        selected_blocks.add(block_position)
        redacted_mask[index] = 1  # Mark this block as redacted
        # redraw_canvas(canvas, image, grid_size, block_size, selected_blocks)

def redraw_canvas(canvas, image, grid_size, block_size, selected_blocks):
    # Update the canvas to show the selected blocks
    canvas.delete("all")
    tk_image = ImageTk.PhotoImage(image)
    canvas.create_image(0, 0, anchor=tk.NW, image=tk_image)
    for block_x, block_y in selected_blocks:
        draw_block(canvas, block_x, block_y, block_size, "red")
    canvas.update()

def draw_block(canvas, block_x, block_y, block_size, outline_color):
    # Calculate the pixel coordinates of the block
    x1 = block_x * block_size
    y1 = block_y * block_size
    x2 = x1 + block_size
    y2 = y1 + block_size

    # Draw a rectangle around the selected block
    canvas.create_rectangle(x1, y1, x2, y2, outline=outline_color, width=2)

def redacttt(image_path, redacted_mask):
    root = tk.Tk()
    root.title("Image Redaction Tool")

    image = load_image(image_path)
    if image is None:
        print("No image loaded.")
        return

    block_size = 10  # Size of each block
    grid_size = (image.width // block_size, image.height // block_size)

    canvas = tk.Canvas(root, width=image.width, height=image.height)
    canvas.pack()

    selected_blocks = set()

    canvas.bind("<Button-1>", lambda event: on_click(event, canvas, grid_size, image, block_size, selected_blocks, redacted_mask))

    def save_transformed_image():
        # Create a copy of the original image
        transformed_image = redact_image(image.copy(), block_size, selected_blocks)
        # Save the transformed image
        save_image(transformed_image, "new_redacted_image.png")
        print("Image saved as 'redacted_image.png'.")
        root.quit()  

    save_button = tk.Button(root, text="Save Image", command=save_transformed_image)
    save_button.pack()

    root.mainloop()

# Example usage
if __name__ == "__main__":
    image_path = get_image_path()
    compressed_original_image = compress_image(image_path)
    # Initialize the redacted mask
    image = load_image(image_path)
    if image:
        grid_size = (image.width // 10, image.height // 10)
        redacted_mask = [0] * (grid_size[0] * grid_size[1])

    out = {
        "original": compressed_original_image,
    }
    redacttt(image_path, redacted_mask)
    compressed_transformed_image = compress_image("new_redacted_image.png")
    out["transformed"] = compressed_transformed_image
    out["redacted_mask"] = redacted_mask
    with open("redact_output.txt", 'w') as fp:
        json.dump(out, fp, indent=4)
    print("Image data dumped successfully.")
