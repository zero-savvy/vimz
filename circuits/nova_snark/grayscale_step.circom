pragma circom 2.2.0;

include "../src/grayscale_step.circom";
include "../src/utils/state.circom";

// NovaSnark wrapper over `GrayScaleHash` circuit.
template NovaGrayScale(width){
    // ---- Running IVC state ----
    input  IVCState step_in;
    output IVCState step_out;
    // ---- Step inputs ----
    signal input row_orig[width], row_tran[width];
    // ---- Step computation ----
    step_out <== GrayScaleHash(width)(step_in, row_orig, row_tran);
}

component main { public [step_in] } = NovaGrayScale(128);
