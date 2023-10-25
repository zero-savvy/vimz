pragma circom 2.0.0;

import "1d_hash.circom";

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
    next_orig_hash <== orig_hash.hash;

    trans_row_hasher.img <== row_trans;
    trans_hasher.values[0] <== prev_trans_hash;
    trans_hasher.values[1] <== trans_row_hasher.hash;
    next_trans_hash <== trans_hash.hash;

    // grayscale code here ...
    
}

component main { public [hasprev_orig_hashh_orig, prev_trans_hash] } = GrayScaleHash(128);



