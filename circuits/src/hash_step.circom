pragma circom 2.1.0;

include "utils/row_hasher.circom";

template Hash(widthOrig){
    // public inputs
    signal input step_in;
    // private inputs
    signal input row_orig [widthOrig];
    // outputs
    signal output step_out;

    step_out <== Hasher(2)(
        step_in,
        RowHasher(widthOrig)(row_orig)
    );
}
