pragma circom 2.0.0;

include "../node_modules/circomlib/circuits/multiplexer.circom";
include "../node_modules/circomlib/circuits/mux1.circom";
include "../node_modules/circomlib/circuits/comparators.circom";
include "utils/pixels.circom";
include "utils/row_hasher.circom";


template CropHash(widthOrig){
    // public inputs
    signal input step_in;
    
    // private inputs
    signal input row_orig [widthOrig];
    
    //outputs
    signal output step_out;
    
    // Decode input Signals
    var prev_orig_hash = step_in;

    // encoding signals
    var next_orig_hash;
    var next_crop_hash;

    component orig_row_hasher = RowHasher(widthOrig);
    component orig_hasher = Hasher(2);

    orig_row_hasher.img <== row_orig;
    orig_hasher.values[0] <== prev_orig_hash;
    orig_hasher.values[1] <== orig_row_hasher.hash;
    next_orig_hash = orig_hasher.hash;

    step_out <== next_orig_hash;    
}

// component main { public [step_in] } = CropHash(768);
