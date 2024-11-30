pragma circom 2.1.0;

include "../src/hash_step.circom";

// Sonobe wrapper over `Hash` circuit.
template SonobeHash(width){
    // ---- Running IVC state ----
    signal input  ivc_input;
    signal output ivc_output;
    // ---- Step inputs ----
    signal input  external_inputs[width];
    // ---- Step computation ----
    ivc_output <== Hash(width)(ivc_input, external_inputs);
}

component main { public [ivc_input] } = SonobeHash(768);
