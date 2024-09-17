import os
from PIL import Image, ImageDraw, ImageTk
import tkinter as tk
from tkinter import filedialog
import numpy as np

def load_image():
    file_path = filedialog.askopenfilename()
    if file_path:
        return Image.open(file_path)
    return None

def save_image(image, file_name):
    image.save(file_name)

def on_click(event, canvas, grid_size, image, block_size, selected_blocks):
    x = event.x // block_size
    y = event.y // block_size
    selected_blocks.add((x, y))
    redraw_canvas(canvas, image, grid_size, block_size, selected_blocks)

def redraw_canvas(canvas, image, grid_size, block_size, selected_blocks):
    canvas.delete("all")
    for x in range(grid_size[0]):
        for y in range(grid_size[1]):
            x1, y1 = x * block_size, y * block_size
            x2, y2 = x1 + block_size, y1 + block_size
            if (x, y) in selected_blocks:
                canvas.create_rectangle(x1, y1, x2, y2, fill="black")
            else:
                block = image.crop((x1, y1, x2, y2))
                block_2 = ImageTk.PhotoImage(block)

                canvas.image = block_2  # Keep a reference to avoid garbage collection
                canvas.create_image(x1, y1, anchor=tk.NW, image=block_2)

def redact_image(image, block_size, selected_blocks):
    draw = ImageDraw.Draw(image)
    for x, y in selected_blocks:
        x1, y1 = x * block_size, y * block_size
        x2, y2 = x1 + block_size, y1 + block_size
        draw.rectangle([x1, y1, x2, y2], fill="black")
    return image



def redacttt():
    root = tk.Tk()
    root.title("Image Redaction Tool")

    image = load_image()
    if image is None:
        print("No image loaded.")
        return

    block_size = 10  # Size of each block
    grid_size = (image.width // block_size, image.height // block_size)

    canvas = tk.Canvas(root, width=image.width, height=image.height)
    canvas.pack()

    selected_blocks = set()

    canvas.bind("<Button-1>", lambda event: on_click(event, canvas, grid_size, image, block_size, selected_blocks))
    redraw_canvas(canvas, image, grid_size, block_size, selected_blocks)

    def save_transformed_image():
        transformed_image = redact_image(image.copy(), block_size, selected_blocks)
        save_image(transformed_image, "redacted_image.png")
        print("Image saved as 'redacted_image.png'.")

    save_button = tk.Button(root, text="Save Image", command=save_transformed_image)
    save_button.pack()

    root.mainloop()

def split_image(image_path, block_size=10):
    # Load the image
    image = Image.open(image_path)
    image_width, image_height = image.size

    # Create a list to hold the block images
    blocks = []

    # Partition the image into blocks
    for y in range(0, image_height, block_size):
        for x in range(0, image_width, block_size):
            # Define the bounding box for the block
            box = (x, y, x + block_size, y + block_size)
            block = image.crop(box)
            blocks.append(block)
    
    return blocks

def save_blocks(blocks, output_dir='blocks'):
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
    
    # Save each block as an image
    for i, block in enumerate(blocks):
        block.save(f"{output_dir}/block_{i}.png")

def show_blocks(blocks):
    print("................ len_blocks: ", len(blocks))
    for index in range(len(blocks)):

        root = tk.Tk()
        root.title("Image Blocks")

        block = blocks[index]
        photo = ImageTk.PhotoImage(block)

        # Create a new window to display the block
        block_window = tk.Toplevel(root)
        block_window.title(f"Block {index}")
        
        # Create a canvas to show the block
        canvas = tk.Canvas(block_window, width=block.width, height=block.height)
        canvas.pack()

        # Display the block
        # canvas.image = photo
        canvas.create_image(0, 0, anchor=tk.NW, image=photo)

        # Keep a reference to the image to prevent it from being garbage-collected
        canvas.image = photo
        root.mainloop()

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

# def save_in_blocks():
#     # Open a file dialog to select the image
#     root = tk.Tk()
#     root.withdraw()  # Hide the root window
#     image_path = filedialog.askopenfilename()
#     if not image_path:
#         print("No image selected")
#         return

#     # Partition, save, and display the image blocks
#     blocks = split_image(image_path, block_size=10)
#     save_blocks(blocks)

#     # show_blocks(blocks)



if __name__ == "__main__":
    image_path = get_image_path()
    compressed_original_image = compress_image(image_path)
    out = {
        "original": compressed_original_image,
    }
    redacttt()
    # compressed_transformed_image = compress_image(image)
