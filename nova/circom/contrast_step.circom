pragma circom 2.0.0;

include "utils/row_hasher.circom";
include "utils/pixels.circom";
include "circomlib/circuits/bitify.circom";


template ContrastChecker(n) {
    signal input orig[n][3];
    signal input tran[n][3];

    signal output n_check;
 
    component lt[n][2];

    for (var i = 0; i < n; i++) {  
        for (var j = 0; j < 3; j++) {  
            
        }
    }
    n_check <== n;
}

template GrayScale(width){
    
    signal input original[width];
    signal input transformed[width];
    
    component decompressor[width];
    component decompressor_grey[width];
    component greychecker[width];

    for (var j=0; j<width; j++) {
        decompressor[j] = Decompressor();
        decompressor[j].in <== original[j];

        decompressor_grey[j] = DecompressorGrey();
        decompressor_grey[j].in <== transformed[j];
        
        greychecker[j] = GrayscaleChecker(10);
        greychecker[j].orig <== decompressor[j].out;
        greychecker[j].gray <== decompressor_grey[j].out;
    }

}

template GrayScaleHash(width){
    signal input step_in[2];
    // signal input prev_orig_hash;
    // signal input prev_gray_hash;
    signal output step_out[2];
    // signal output next_orig_hash;
    // signal output next_gray_hash;
    
    // Private inputs
    signal input row_orig [width];
    signal input row_gray [width];
    
    component orig_row_hasher = RowHasher(width);
    component gray_row_hasher = RowHasher(width);
    component orig_hasher = Hasher(2);
    component gray_hasher = Hasher(2);

    orig_row_hasher.img <== row_orig;
    orig_hasher.values[0] <== step_in[0]; // prev_orig_hash
    orig_hasher.values[1] <== orig_row_hasher.hash;
    step_out[0] <== orig_hasher.hash; // next_orig_hash

    gray_row_hasher.img <== row_gray;
    gray_hasher.values[0] <== step_in[1]; // prev_gray_hash
    gray_hasher.values[1] <== gray_row_hasher.hash;
    step_out[1] <== gray_hasher.hash; // next_grey_hash

    // grayscale code here ...
    component checker = GrayScale(width);
    checker.original <== row_orig;
    checker.transformed <== row_gray;

}

component main { public [step_in] } = GrayScaleHash(128);



