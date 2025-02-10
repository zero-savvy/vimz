pragma circom 2.2.0;

include "hashers.circom";
include "pixels.circom";
include "../../node_modules/circomlib/circuits/bitify.circom";
include "../../node_modules/circomlib/circuits/comparators.circom";
include "../../node_modules/circomlib/circuits/multiplexer.circom";
include "../../node_modules/circomlib/circuits/mux1.circom";

template UnwrapAndExtend(width, kernel_size) {
    signal input row_orig[kernel_size][width];
    signal input row_conv[width];
        
    var decompressedWidth = width * 10;
    var extendedWidth = decompressedWidth + kernel_size - 1;

    signal output out_orig[kernel_size][extendedWidth][3];
    signal output out_conv [decompressedWidth][3];

    component decompressor_orig[kernel_size][width];
    for (var k = 0; k < kernel_size; k++) {
        for (var i = 0; i < kernel_size \ 2; i++) {
            out_orig[k][i][0] <== 0;  // R
            out_orig[k][i][1] <== 0;  // G
            out_orig[k][i][2] <== 0;  // B

            out_orig[k][extendedWidth - i - 1][0] <== 0;  // R
            out_orig[k][extendedWidth - i - 1][1] <== 0;  // G
            out_orig[k][extendedWidth - i - 1][2] <== 0;  // B
        }
        for (var i = 0; i < width; i++) {
            decompressor_orig[k][i] = Decompressor();
            decompressor_orig[k][i].in <== row_orig[k][i];
            for (var j = 0; j < 10; j++) {
                out_orig[k][(kernel_size\2)+i*10+j] <== decompressor_orig[k][i].out[j];
            }
        }
    }

    component decompressor_conv[width];
    for (var i = 0; i < width; i++) {
        decompressor_conv[i] = Decompressor();
        decompressor_conv[i].in <== row_conv[i];
        for (var j = 0; j < 10; j++) {
            out_conv[i*10+j] <== decompressor_conv[i].out[j];
        }
    }
}
