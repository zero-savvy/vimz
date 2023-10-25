pragma circom 2.0.0;

include "row_hasher.circom";
include "../../circom/utils/pixels.circom";
include "../../circom/round.circom";


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



