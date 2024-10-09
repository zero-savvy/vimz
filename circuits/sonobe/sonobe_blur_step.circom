pragma circom 2.1.0;

include "../src/blur_step.circom";
include "../src/utils/input_transformation.circom";

// Sonobe wrapper over `Blur` circuit.
template SonobeBlur(width, kernel_size){
    signal input  external_inputs[kernel_size * width + width];
    signal input  ivc_input[4];
    signal output ivc_output[4];

    signal row_orig[kernel_size][width], row_tran[width];
    (row_orig, row_tran) <== KernelInput(width, kernel_size)(external_inputs);

    ivc_output <== Blur(width, kernel_size)(ivc_input, row_orig, row_tran);
}

component main { public [ivc_input] } = SonobeBlur(128, 3);
