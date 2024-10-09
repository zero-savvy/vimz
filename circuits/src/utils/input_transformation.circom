pragma circom 2.1.0;

// Splits a combined input array into two separate rows of signals.
//
// Parameters:
// - `width`: Number of elements in each of the output rows (`row_orig` and `row_tran`).
//
// Signals:
// - `input full_input[2 * width]`: Combined input array of size `2 * width`,
//   containing values for both `row_orig` and `row_tran`.
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