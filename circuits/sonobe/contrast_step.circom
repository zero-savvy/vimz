pragma circom 2.2.0;

include "../src/contrast_step.circom";
include "../src/utils/input_transformation.circom";

// Sonobe wrapper over `ContrastHash` circuit.
template SonobeContrast(width){
    // ---- Running IVC state ----
    signal input  ivc_input[3];
    signal output ivc_output[3];
    // ---- Step inputs ----
    signal input  external_inputs[2 * width];
    // ---- Input transformation ----
    signal row_orig[width], row_tran[width];
    (row_orig, row_tran) <== SimpleInput(width)(external_inputs);
    // ---- Step computation ----
    ivc_output <== ContrastHash(width)(ivc_input, row_orig, row_tran);
}

component main { public [ivc_input] } = SonobeContrast(128);
