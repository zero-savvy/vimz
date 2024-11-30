pragma circom 2.1.0;

include "../src/utils/hashers.circom";

// Compute running hash for a row of pixels.
template SonobeHash(width){
    // ---- Running IVC state ----
    signal input  ivc_input;
    signal output ivc_output;
    // ---- Step inputs ----
    signal input  external_inputs[width];
    // ---- Step computation ----
    ivc_output <== HeadTailHasher(width)(ivc_input, external_inputs);
}

component main { public [ivc_input] } = SonobeHash(768);
