pragma circom 2.2.0;

include "../src/sharpness_step.circom";
include "../src/utils/input_transformation.circom";

// Sonobe wrapper over `Sharpen` circuit.
template SonobeSharpness(width, kernel_size){
    // ---- Running IVC state ----
    signal input  ivc_input[4];
    signal output ivc_output[4];
    // ---- Step inputs ----
    signal input  external_inputs[kernel_size * width + width];
    // ---- Input transformation ----
    signal row_orig[kernel_size][width], row_tran[width];
    (row_orig, row_tran) <== KernelInput(width, kernel_size)(external_inputs);
    // ---- Step computation ----
    ivc_output <== Sharpen(width, kernel_size)(ivc_input, row_orig, row_tran);
}

component main { public [ivc_input] } = SonobeSharpness(128, 3);
