pragma circom 2.1.0;

include "utils/row_hasher.circom";

template Hash(widthOrig){
    // public inputs
    signal input step_in;
    // private inputs
    signal input row_orig [widthOrig];
    // outputs
    signal output step_out;

    component hasher = Hasher(2);
    hasher.values[0] <== step_in;
    hasher.values[1] <== RowHasher(widthOrig)(row_orig);
    step_out <== hasher.hash;
}
