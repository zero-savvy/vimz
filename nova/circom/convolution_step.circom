pragma circom 2.0.0;

include "utils/row_hasher.circom";
include "utils/pixels.circom";
include "circomlib/circuits/bitify.circom";


template Convolve(width, kernel_size){
    
    signal input row_orig[kernel_size][width];
    signal input row_conv[width];
    // signal input kernel[kernel_size][kernel_size];

    var kernel[kernel_size][kernel_size];
    kernel [0][0] = 0;
    kernel [0][1] = 0;
    kernel [0][2] = 0;
    kernel [1][0] = 0;
    kernel [1][1] = 1;
    kernel [1][2] = 0;
    kernel [2][0] = 0;
    kernel [2][1] = 0;
    kernel [2][2] = 0;
    
    // ASSERT the Kernel matrice to be an sqaure of odd size
    // kernel_wdith === kernel_height;
    1 === kernel_size % 2;

    // signal target_pixel_location <== (kernel_size \ 2) + 1; 
    
    
    var decompressedWidth = width * 10;
    var extendedWidth = decompressedWidth + kernel_size - 1;

    signal decompressed_row_orig [kernel_size][extendedWidth][3];
    component decompressor_orig[kernel_size][width];
    for (var k = 0; k < kernel_size; k++) {
        for (var i = 0; i < kernel_size \ 2; i++) {
            decompressed_row_orig[k][i][0] <== 0;  // R
            decompressed_row_orig[k][i][1] <== 0;  // G
            decompressed_row_orig[k][i][2] <== 0;  // B

            decompressed_row_orig[k][extendedWidth - i - 1][0] <== 0;  // R
            decompressed_row_orig[k][extendedWidth - i - 1][1] <== 0;  // G
            decompressed_row_orig[k][extendedWidth - i - 1][2] <== 0;  // B
        }
        for (var i = 0; i < width; i++) {
            decompressor_orig[k][i] = Decompressor();
            decompressor_orig[k][i].in <== row_orig[k][i];
            for (var j = 0; j < 10; j++) {
                decompressed_row_orig[k][(kernel_size\2)+i*10+j] <== decompressor_orig[k][i].out[j];
            }
        }
    }

    signal decompressed_row_conv [decompressedWidth][3];
    component decompressor_conv[width];
    for (var i = 0; i < width; i++) {
        decompressor_conv[i] = Decompressor();
        decompressor_conv[i].in <== row_conv[i];
        for (var j = 0; j < 10; j++) {
            decompressed_row_conv[i*10+j] <== decompressor_conv[i].out[j];
        }
    }

    // ----------------------------
    // Execute Convolution
    // ----------------------------
    // var target_pixel_location = kernel_size \ 2 + 1;
    var conv_value;
    var weight = 1;  // TODO: weights other than 1

    for (var color = 0; color < 3; color++) {
        for (var i = 0; i < decompressedWidth; i++) {
            conv_value = 0;
            for (var m = 0; m < kernel_size; m++) {
                for (var n = 0; n < kernel_size; n++) {
                    conv_value += decompressed_row_orig[m][i + n][color] * kernel[m][n];
                }
            }
            log(decompressed_row_conv[i][color], conv_value);
            decompressed_row_conv[i][color] * weight === conv_value;
        }
    }
}

template ConvolveHash(width, kernel_size){
    // public inputs and outputs
    signal input step_in[kernel_size+2];
    // signal input prev_orig_hash_0;
    // signal input prev_orig_hash_1;
    // signal input prev_orig_hash_2;
    // signal input prev_orig_hash_3;
    // signal input prev_orig_hash;
    // signal input prev_conv_hash;
    // signal input compressed_kernel;
    
    signal output step_out[kernel_size+2];
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

    var row_hashes[kernel_size];

    component orig_row_hasher[kernel_size];
    component orig_hasher;

    for (var i = 0; i < kernel_size; i++) {
        orig_row_hasher[i] = RowHasher(width);
        orig_row_hasher[i].img <== row_orig[i];
        row_hashes[i] = orig_row_hasher[i].hash;
    }

    orig_hasher = Hasher(2);
    orig_hasher.values[0] <== step_in[kernel_size-1];
    orig_hasher.values[1] <== row_hashes[(kernel_size \ 2) + 1]; // hash with hash of middle row  
    step_out[kernel_size-1] <== orig_hasher.hash;

    component conv_row_hasher;
    component conv_hasher;

    conv_row_hasher = RowHasher(width);
    conv_row_hasher.img <== row_conv;

    conv_hasher = Hasher(2);
    conv_hasher.values[0] <== step_in[kernel_size];
    conv_hasher.values[1] <== conv_row_hasher.hash; 
    step_out[kernel_size] <== conv_hasher.hash;

    for (var i = 0; i < kernel_size-1; i++) {
        // row_hashes[i] === step_in[i];
        step_out[i] <== row_hashes[i+1]; 
    }

    component decompressor_kernel = DecompressorKernel(kernel_size);
    decompressor_kernel.in <== step_in[kernel_size+1];

    component conv_checker = Convolve(width, kernel_size);
    conv_checker.row_orig <== row_orig;
    conv_checker.row_conv <== row_conv;
    // conv_checker.kernel <== decompressor_kernel.out;
}

component main { public [step_in] } = ConvolveHash(128, 3);



