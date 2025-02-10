pragma circom 2.2.0;

include "utils/convolution_step.circom";

template Sharpen(width, kernel_size){
    // public inputs and outputs
    signal input step_in[kernel_size+1];
    // signal input prev_orig_hash_0;
    // signal input prev_orig_hash_1;
    // signal input prev_orig_hash_2;
    // signal input prev_orig_hash_3;
    // signal input prev_orig_hash;
    // signal input prev_conv_hash;
    // signal input compressed_kernel;
    
    signal output step_out[kernel_size+1];
    // signal output next_orig_hash_1;
    // signal output next_orig_hash_2;
    // signal output next_orig_hash_3;
    // signal output next_orig_hash_4;
    // signal output next_orig_hash;
    // signal output next_conv_hash;
    // signal output compressed_kernel;
    
    // private inputs
    signal input row_orig [kernel_size][width];
    signal input row_tran [width];

    component integrity_checker = IntegrityCheck(width, kernel_size);
    integrity_checker.step_in <== step_in;
    integrity_checker.row_orig <== row_orig;
    integrity_checker.row_conv <== row_tran;
    step_out <== integrity_checker.step_out;

    SharpenCheck(width, kernel_size)(row_orig, row_tran);
}

template SharpenCheck(width, kernel_size) {
    signal input row_orig[kernel_size][width];
    signal input row_conv[width];

    component unwrapper = UnwrapAndExtend(width, kernel_size);
    unwrapper.row_orig <== row_orig;
    unwrapper.row_conv <== row_conv;

    // ----------------------------
    // Execute Convolution
    // ----------------------------
    var decompressedWidth = width * 10;
    ConvolveSharpen(decompressedWidth)(unwrapper.out_orig, unwrapper.out_conv);
}

template ConvolveSharpen(decompressedWidth) {
    var kernel_size = 3;

    signal input decompressed_row_orig[kernel_size][decompressedWidth + kernel_size -1][3];
    signal input decompressed_row_conv[decompressedWidth][3];

    var kernel[kernel_size][kernel_size];
        kernel [0][0] = 0;
        kernel [0][1] = -1;
        kernel [0][2] = 0;
        kernel [1][0] = -1;
        kernel [1][1] = 5;
        kernel [1][2] = -1;
        kernel [2][0] = 0;
        kernel [2][1] = -1;
        kernel [2][2] = 0;

    var weight = 1;

    component lt[decompressedWidth][3][2];
    component ltt[decompressedWidth][3][2];
    component selector[decompressedWidth][3];
    component gt_selector[decompressedWidth][3];

    for (var color = 0; color < 3; color++) {
        for (var i = 0; i < decompressedWidth; i++) {
            var conv_value = 0;
            for (var m = 0; m < kernel_size; m++) {
                for (var n = 0; n < kernel_size; n++) {
                    if (kernel[m][n] != 0) {
                        conv_value += decompressed_row_orig[m][i + n][color] * kernel[m][n];
                    }
                }
            }

            // Clip the value to [0..255] range
            // find sign of r_adjusted
            ltt[i][color][0] = LessEqThan(12);
            ltt[i][color][1] = LessEqThan(12);
            ltt[i][color][0].in[1] <== 0 - conv_value;
            ltt[i][color][0].in[0] <==  conv_value;
            ltt[i][color][1].in[0] <== 255;
            ltt[i][color][1].in[1] <==  conv_value;

            gt_selector[i][color] = Mux1();
            gt_selector[i][color].c[1] <== 255;
            gt_selector[i][color].c[0] <== conv_value;
            gt_selector[i][color].s <== ltt[i][color][1].out;

            selector[i][color] = Mux1();
            selector[i][color].c[0] <== gt_selector[i][color].out;
            selector[i][color].c[1] <== 0;
            selector[i][color].s <== ltt[i][color][0].out;

            var final_value = selector[i][color].out;

            lt[i][color][0] = LessEqThan(9);
            lt[i][color][0].in[0] <== final_value - decompressed_row_conv[i][color];
            lt[i][color][0].in[1] <== 1;
            lt[i][color][1] = LessEqThan(9);
            lt[i][color][1].in[0] <== decompressed_row_conv[i][color] - final_value;
            lt[i][color][1].in[1] <== 1;

            lt[i][color][0].out === 1;
            lt[i][color][1].out === 1;
        }
    }
}
