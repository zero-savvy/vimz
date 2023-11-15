pragma circom 2.0.0;

include "utils/row_hasher.circom";
include "utils/pixels.circom";
include "circomlib/circuits/bitify.circom";


template GrayscaleChecker(n) {
    signal input orig[n][3];
    signal input gray[n];

    signal output n_check;
 
    component lt[n][2];

    for (var i = 0; i < n; i++) {      
        var inter = 299 * orig[i][0] + 587 * orig[i][1] + 114 * orig[i][2];

        lt[i][0] = LessEqThan(16);
        lt[i][1] = LessEqThan(16);

        lt[i][0].in[1] <== 1000;
        lt[i][0].in[0] <== inter - 1000 * gray[i];
        lt[i][0].out === 1;

        lt[i][1].in[1] <== 1000;
        lt[i][1].in[0] <== 1000 * gray[i] - inter;
        lt[i][1].out === 1; 
    }
    n_check <== n;
}

template Convolve(width, kernel_size){
    
    signal input row_orig[kernel_size][width];
    signal input row_conv[width];
    signal input kernel[kernel_size][kernel_size];
    
    // ASSERT the Kernel matrice to be an sqaure of odd size
    // kernel_wdith === kernel_height;
    1 === kernel_size % 2;

    signal target_pixel_location <== (kernel_size \ 2) + 1; 
    
    
    var decompressedWidth = width * 10;
    signal decompressed_row_orig [kernel_size][decompressedWidth][3];
    signal decompressed_row_tran [kernel_size][decompressedWidth][3];

    component decompressor_orig[kernel_height][width];
    component decompressor_tran[kernel_height][width];
    for (var k = 0; k < kernel_height; k++) {
        for (var i = 0; i < width; i++) {
            decompressor_orig[k][i] = Decompressor();
            decompressor_orig[k][i].in <== row_orig[k][i];
            decompressor_tran[k][i] = Decompressor();
            decompressor_tran[k][i].in <== row_tran[k][i];
            for (var j = 0; j < 10; j++) {
                decompressed_row_orig[k][i*10+j] <== decompressor_orig[k][i].out[j];
                decompressed_row_tran[k][i*10+j] <== decompressor_tran[k][i].out[j];
            }
        }
    }

    // ----------------------------
    // Execute Convolution
    // ----------------------------
    var target_pixel_location = kernel_size \ 2 + 1;
    var conv_value;

    for (var c = 0; c < 3; c++) {
        for (var i = 0; i < decompressedWidth; i++) {
            conv_value = 0;
            for (var m = 0; m < kernel_size) {
                for ( var n = 0; n < kernel_size) {
                    conv_value += row_orig[i + m][j + n] * kernel[m][n];
                }
            }
            convolved_array[i][j] = conv_value // weight

        }
    }
    


}

template ConvolveHash(width, kernel_size){
    // public inputs and outputs
    signal input step_in[kernel_size+3];
    // signal input prev_orig_hash_0;
    // signal input prev_orig_hash_1;
    // signal input prev_orig_hash_2;
    // signal input prev_orig_hash_3;
    // signal input prev_orig_hash;
    // signal input prev_conv_hash;
    // signal input compressed_kernel;
    // signal input row_index;
    
    signal output step_out[kernel_size+3];
    // signal output next_orig_hash_1;
    // signal output next_orig_hash_2;
    // signal output next_orig_hash_3;
    // signal output next_orig_hash_4;
    // signal output next_orig_hash;
    // signal output next_conv_hash;
    // signal output compressed_kernel;
    // signal output row_index;
    
    // private inputs
    signal input row_orig [kernel_size][width];
    signal input row_conv [width];

    var row_hashes[kernel_size];

    component orig_row_hasher[kernel_size];
    component orig_hasher;

    for (var i = 0; i < kernel_size; i++) {
        orig_row_hasher[i] = RowHasher(width);
        orig_row_hasher[i].img <== row_orig[i];
        row_hashes[i] = orig_row_hasher[i].hash;
    }

    orig_hasher = Hasher(2);
    orig_hasher.values[0] <== prev_orig_hash;
    orig_hasher.values[1] <== row_hashes[(kernel_size \ 2) + 1]; // hash with hash of middle row  
    next_orig_hash <== orig_hasher.hash;

    component conv_row_hasher;
    component conv_hasher;

    conv_row_hasher = RowHasher(width);
    conv_row_hasher.img <== row_conv;

    conv_hasher = Hasher(2);
    conv_hasher.values[0] <== prev_conv_hash;
    conv_hasher.values[1] <== conv_row_hasher.hash; 
    next_conv_hash <== conv_hasher.hash;

    for (var i = 0; i < kernel_size-1; i++) {
        row_hashes[i] === step_in[i];
        step_out[i] <== row_hashes[i+1]; 
    }

    component decompressor_kernel = 

    component conv_checker = Convolve(width, kernel_size);
    conv_checker.row_orig <== row_orig;
    conv_checker.row_conv <== row_conv;
    conv_checker.kernel <== kernel;
}

component main { public [step_in] } = ConvolveHash(128);



