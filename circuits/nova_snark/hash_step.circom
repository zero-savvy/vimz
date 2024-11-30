pragma circom 2.1.0;

include "../src/utils/hashers.circom";

// Compute running hash for a row of pixels.
template NovaHash(width){
    // ---- Running IVC state ----
    signal input  step_in;
    signal output step_out;
    // ---- Step inputs ----
    signal input row_orig [width];
    // ---- Step computation ----
    step_out <== HeadTailHasher(width)(step_in, row_orig);
}

component main { public [step_in] } = NovaHash(768);
