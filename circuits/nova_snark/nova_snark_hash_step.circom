pragma circom 2.1.0;

include "../src/hash_step.circom";

// NovaSnark wrapper over `Hash` circuit.
template NovaHash(width){
    // ---- Running IVC state ----
    signal input  step_in;
    signal output step_out;
    // ---- Step inputs ----
    signal input row_orig [width];
    // ---- Step computation ----
    step_out <== Hash(width)(step_in, row_orig);
}

component main { public [step_in] } = NovaHash(768);
