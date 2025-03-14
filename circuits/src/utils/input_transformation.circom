pragma circom 2.2.0;

// Splits a combined input array into two separate rows of signals.
//
// Parameters:
// - `width`: Number of elements in each of the output rows (`row_orig` and `row_tran`).
//
// Signals:
// - `input full_input[2 * width]`: Combined input array.
// - `output row_orig[width]`: The first half of `full_input` (first `width` elements).
// - `output row_tran[width]`: The second half of `full_input` (last `width` elements).
template SimpleInput(width) {
    signal input  full_input [2 * width];
    signal output row_orig   [width];
    signal output row_tran   [width];

    for (var i = 0; i < width; i++) {
        row_orig[i] <== full_input[i];
        row_tran[i] <== full_input[i + width];
    }
}

// Splits a combined input array into two separate signals, where the first is a 2D array, the second is a 1D array.
//
// Parameters:
// - `width`: Number of elements in each of the output rows (`row_orig` and `row_tran`).
// - `kernel_size`: Number of rows in the 2D array.
//
// Signals:
// - `input full_input[kernel_size * width + width]`: Combined input array.
// - `output row_orig[kernel_size][width]`: The first `kernel_size * width` elements of `full_input`,
//   reshaped into a 2D array.
// - `output row_tran[width]`: The last `width` elements of `full_input`.
template KernelInput(width, kernel_size) {
    signal input  full_input [kernel_size * width + width];
    signal output row_orig   [kernel_size][width];
    signal output row_tran   [width];

    for (var i = 0; i < width; i++) {
        for (var j = 0; j < kernel_size; j++) {
            row_orig[j][i] <== full_input[j * width + i];
        }
        row_tran[i] <== full_input[i + kernel_size * width];
    }
}

// Splits a combined input array into two separate 2D arrays.
//
// Parameters:
// - `widthOrig`: Number of elements in each row of the first output array (`row_orig`).
// - `widthResized`: Number of elements in each row of the second output array (`row_tran`).
// - `rowCountOrig`: Number of rows in the first output array.
// - `rowCountResized`: Number of rows in the second output array.
//
// Signals:
// - `input full_input[widthOrig * rowCountOrig + widthResized * rowCountResized]`: Combined input array.
// - `output row_orig[rowCountOrig][widthOrig]`: The first `widthOrig * rowCountOrig` elements of `full_input`,
//   reshaped into a 2D array.
// - `output row_tran[rowCountResized][widthResized]`: The last `widthResized * rowCountResized` elements of `full_input`,
//   reshaped into a 2D array.
template ResizeInput(widthOrig, widthResized, rowCountOrig, rowCountResized) {
    signal input  full_input [widthOrig * rowCountOrig + widthResized * rowCountResized];
    signal output row_orig   [rowCountOrig][widthOrig];
    signal output row_tran   [rowCountResized][widthResized];

    for (var i = 0; i < widthOrig; i++) {
        for (var j = 0; j < rowCountOrig; j++) {
            row_orig[j][i] <== full_input[j * widthOrig + i];
        }
    }
    for (var i = 0; i < widthResized; i++) {
        for (var j = 0; j < rowCountResized; j++) {
            row_tran[j][i] <== full_input[j * widthResized + i + widthOrig * rowCountOrig];
        }
    }
}

// Splits a combined input array into an array and a scalar.
//
// Parameters:
// - `arraySize`: Number of elements in the output array (hence, expected input should have `arraySize` + 1 entries).
//
// Signals:
// - `input full_input[arraySize + 1]`: Combined input array.
// - `output array[arraySize]`: The first `arraySize` elements of `full_input`.
// - `output scalar`: The last element of `full_input`.
template ArrayWithScalarInput(arraySize) {
    signal input  full_input [arraySize + 1];

    signal output array [arraySize];
    for (var i = 0; i < arraySize; i++) {
        array[i] <== full_input[i];
    }

    signal output scalar <== full_input[arraySize];
}
