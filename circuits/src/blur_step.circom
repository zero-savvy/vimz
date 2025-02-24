pragma circom 2.2.0;

include "utils/convolution_step.circom";
include "utils/state.circom";

template Blur(width, kernel_size) {
    input  IVCStateConv(kernel_size) step_in;
    output IVCStateConv(kernel_size) step_out;

    // Private inputs
    signal input row_orig [kernel_size][width];
    signal input row_tran [width];

    // Execute the step
    BlurCheck(width, kernel_size)(row_orig, row_tran);
    // Update IVC state
    step_out <== UpdateIVCStateConv(kernel_size, width)(step_in, row_orig, row_tran);
}

template BlurCheck(width, kernel_size) {
    signal input row_orig[kernel_size][width];
    signal input row_conv[width];

    component unwrapper = UnwrapAndExtend(width, kernel_size);
    unwrapper.row_orig <== row_orig;
    unwrapper.row_conv <== row_conv;

    var decompressedWidth = width * 10;
    ConvolveBlur(decompressedWidth)(unwrapper.out_orig, unwrapper.out_conv);
}

template ConvolveBlur(decompressedWidth) {
    var kernel_size = 3;

    signal input decompressed_row_orig[kernel_size][decompressedWidth + kernel_size -1][3];
    signal input decompressed_row_conv[decompressedWidth][3];

    var kernel[kernel_size][kernel_size];
        kernel [0][0] = 1;
        kernel [0][1] = 1;
        kernel [0][2] = 1;
        kernel [1][0] = 1;
        kernel [1][1] = 1;
        kernel [1][2] = 1;
        kernel [2][0] = 1;
        kernel [2][1] = 1;
        kernel [2][2] = 1;

    var weight = 9;

    component lt[decompressedWidth][3][2];

    for (var color = 0; color < 3; color++) {
        for (var i = 0; i < decompressedWidth; i++) {
            var conv_value = 0;
            for (var m = 0; m < kernel_size; m++) {
                for (var n = 0; n < kernel_size; n++) {
                    conv_value += decompressed_row_orig[m][i + n][color]; // * kernel[m][n]; --> because all kernel values are 1 in blur!
                }
            }
            lt[i][color][0] = LessEqThan(13);

            lt[i][color][0].in[0] <== conv_value - decompressed_row_conv[i][color] * weight;
            lt[i][color][0].in[1] <== weight;
            lt[i][color][1] = LessEqThan(13);
            lt[i][color][1].in[0] <== decompressed_row_conv[i][color] * weight - conv_value;
            lt[i][color][1].in[1] <== weight;

            lt[i][color][0].out === 1;
            lt[i][color][1].out === 1;
        }
    }
}
