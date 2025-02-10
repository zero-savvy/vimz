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

template IntegrityCheck(width, kernel_size) {
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
    signal input row_conv [width];

    signal row_hashes[kernel_size];
    for (var i = 0; i < kernel_size; i++) {
        row_hashes[i] <== ArrayHasher(width)(row_orig[i]);
    }
    
    step_out[kernel_size-1] <== PairHasher()(
        step_in[kernel_size-1],
        row_hashes[(kernel_size \ 2) + 1] // hash with hash of middle row
    );

    step_out[kernel_size] <== HeadTailHasher(width)(step_in[kernel_size], row_conv);

    component zero_checker[kernel_size - 1];
    for (var i = 0; i < kernel_size-1; i++) {
        zero_checker[i] = IsZero();
        zero_checker[i].in <== step_in[i];
        row_hashes[i] * (1 - zero_checker[i].out) === step_in[i];
        step_out[i] <== row_hashes[i+1]; 
    }

}

// component main { public [step_in] } = IntegrityCheck(128, 3);