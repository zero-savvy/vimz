pragma circom 2.1.0;

include "../src/grayscale_step.circom";
include "../src/utils/input_transformation.circom";

// Sonobe wrapper over `GrayScaleHash` circuit.
template SonobeGrayScaleHash(width){
    signal input  external_inputs[2 * width];
    signal input  ivc_input[2];
    signal output ivc_output[2];

    signal row_orig[width], row_tran[width];
    (row_orig, row_tran) <== SimpleInput(width)(external_inputs);

    ivc_output <== GrayScaleHash(width)(ivc_input, row_orig, row_tran);
}

component main { public [ivc_input] } = SonobeGrayScaleHash(128);
