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
        var inter = 30 * orig[i][0] + 59 * orig[i][1] + 11 * orig[i][2];

        lt[i][0] = LessEqThan(16);
        lt[i][1] = LessEqThan(16);

        lt[i][0].in[1] <== 100;
        lt[i][0].in[0] <== inter - 100 * gray[i];
        lt[i][0].out === 1;

        lt[i][1].in[1] <== 100;
        lt[i][1].in[0] <== 100 * gray[i] - inter;
        lt[i][1].out === 1; 
    }
    n_check <== n;
}

template GreyScale(width){
    
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
    signal input prev_orig_hash;
    signal input prev_trans_hash;
    signal input row_orig [width];
    signal input row_trans [width];
    signal output next_orig_hash;
    signal output next_trans_hash;

    component orig_row_hasher = RowHasher(width);
    component trans_row_hasher = RowHasher(width);
    component orig_hasher = Hasher(2);
    component trans_hasher = Hasher(2);

    orig_row_hasher.img <== row_orig;
    orig_hasher.values[0] <== prev_orig_hash;
    orig_hasher.values[1] <== orig_row_hasher.hash;
    next_orig_hash <== orig_hasher.hash;

    trans_row_hasher.img <== row_trans;
    trans_hasher.values[0] <== prev_trans_hash;
    trans_hasher.values[1] <== trans_row_hasher.hash;
    next_trans_hash <== trans_hasher.hash;

    // grayscale code here ...
    component checker = GreyScale(width);
    checker.original <== row_orig;
    checker.transformed <== row_trans;

}

component main { public [prev_orig_hash, prev_trans_hash] } = GrayScaleHash(128);



