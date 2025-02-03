pragma circom 2.2.0;

include "../src/grayscale_step.circom";
include "../src/utils/input_transformation.circom";
include "../src/utils/state.circom";

// Sonobe wrapper over `GrayScaleHash` circuit.
template SonobeGrayScale(width){
    // ---- Running IVC state ----
    input  IVCState ivc_input;
    output IVCState ivc_output;
    // ---- Step inputs ----
    signal input  external_inputs[2 * width];
    // ---- Input transformation ----
    signal row_orig[width], row_tran[width];
    (row_orig, row_tran) <== SimpleInput(width)(external_inputs);
    // ---- Step computation ----
    ivc_output <== GrayScaleHash(width)(ivc_input, row_orig, row_tran);
}

component main { public [ivc_input] } = SonobeGrayScale(128);
