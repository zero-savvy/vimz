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

template Convolve(width, kernel_height, kernel_wdith){
    
    signal input row_orig[kernel_height][width];
    signal input row_tran[kernel_height][width];
    
    // ASSERT the Kernel matrice to be an sqaure of odd size
    kernel_wdith === kernel_height;
    1 === kernel_height % 2;

    signal target_pixel_location <== (kernel_height \ 2) + 1; 
    
    signal input kernel[kernel_height][kernel_wdith];
    
    var decompressedWidth = width * 10;
    signal decompressed_row_orig [kernel_height][decompressedWidth][3];
    signal decompressed_row_tran [kernel_height][decompressedWidth][3];

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
    var target_pixel_location = kernel_height \ 2 + 1;
    var conv_value;

    for (var c = 0; c < 3; c++) {
        for (var i = 0; i < decompressedWidth; i++) {
            conv_value = 0;
            for (var m = 0; m < kernel_height) {
                for ( var n = 0; n < kernel_width) {
                    conv_value += row_orig[i + m][j + n] * kernel[m][n];
                }
            }
            convolved_array[i][j] = conv_value // weight

        }
    }
    


}

template ConvolveHash(width){
    // public inputs
    signal input step_in[2];
    
    // private inputs
    signal input row_orig [rowCountOrig][widthOrig];
    signal input row_resized [rowCountResized][widthResized];

    //outputs
    signal output step_out[2];
    
    // decoding signals
    signal prev_orig_hash <== step_in[0];
    signal prev_resized_hash <== step_in[1];
    
    // encoding signals
    signal next_orig_hash;
    signal next_resized_hash;
    
    component row_hasher_orig[rowCountOrig];
    component hasher_orig [rowCountOrig];
    for (var i = 0; i < rowCountOrig; i++) {
        row_hasher_orig[i] = RowHasher(widthOrig);
        hasher_orig[i] = Hasher(2);
    }

    component row_hasher_resized[rowCountResized];
    component hasher_resized [rowCountResized];
    for (var i = 0; i < rowCountResized; i++) {
        row_hasher_resized[i] = RowHasher(widthResized);
        hasher_resized[i] = Hasher(2);
    } 

    for (var i = 0; i < rowCountOrig; i++) {
        row_hasher_orig[i].img <== row_orig[i];
        hasher_orig[i].values[0] <== i == 0 ? prev_orig_hash : hasher_orig[i-1].hash;
        hasher_orig[i].values[1] <== row_hasher_orig[i].hash;
    }
    next_orig_hash <== hasher_orig[rowCountOrig-1].hash;


}

component main { public [step_in] } = GrayScaleHash(128);



