pragma circom 2.2.0;

include "../src/sharpness_step.circom";
include "../src/utils/state.circom";

// NovaSnark wrapper over `Sharpen` circuit.
template NovaSharpness(width, kernel_size){
    // ---- Running IVC state ----
    input  IVCStateConv(kernel_size) step_in;
    output IVCStateConv(kernel_size) step_out;
    // ---- Step inputs ----
    signal input row_orig[kernel_size][width], row_tran[width];
    // ---- Step computation ----
    step_out <== Sharpen(width, kernel_size)(step_in, row_orig, row_tran);
}

component main { public [step_in] } = NovaSharpness(128, 3);
