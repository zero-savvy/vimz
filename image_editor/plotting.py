import matplotlib.pyplot as plt


def plot_images_side_by_side(np_image1, np_image2, titles=("Original", "Transformed"), max_width=1000):
    """
    Plot two NumPy array images side by side with auto-adjusted figure size.

    Args:
        np_image1 (numpy.ndarray): The first input image as a NumPy array.
        np_image2 (numpy.ndarray): The second input image as a NumPy array.
        titles (tuple): Titles for the subplots. Defaults to ("Original", "Transformed").
        max_width (int): Desired total width of the figure in pixels. Defaults to 1000.

    Returns:
        None
    """
    # Retrieve dimensions of the images
    height1, width1 = np_image1.shape[:2]
    height2, width2 = np_image2.shape[:2]

    # Calculate combined dimensions
    total_width = width1 + width2
    max_height = max(height1, height2)

    # Compute scaling factor to adjust the total width
    scaling_factor = max_width / total_width

    # Set figure size in inches (1 inch = 80 pixels)
    fig_width = max_width / 80
    fig_height = max_height * scaling_factor / 80

    # Create the plot
    plt.figure(figsize=(fig_width, fig_height))

    # Plot the first image
    plt.subplot(1, 2, 1)
    plt.imshow(np_image1, cmap='gray' if np_image1.ndim == 2 else None)
    plt.title(titles[0])
    plt.axis('off')

    # Plot the second image
    plt.subplot(1, 2, 2)
    plt.imshow(np_image2, cmap='gray' if np_image2.ndim == 2 else None)
    plt.title(titles[1])
    plt.axis('off')

    # Display the plot
    plt.tight_layout()
    plt.show()
