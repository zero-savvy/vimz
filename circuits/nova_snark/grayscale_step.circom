pragma circom 2.1.0;

include "../src/grayscale_step.circom";

// NovaSnark wrapper over `GrayScaleHash` circuit.
template NovaGrayScaleHash(width){
    // ---- Running IVC state ----
    signal input  step_in[2];
    signal output step_out[2];
    // ---- Step inputs ----
    signal input row_orig[width], row_tran[width];
    // ---- Step computation ----
    step_out <== GrayScaleHash(width)(step_in, row_orig, row_tran);
}

component main { public [step_in] } = NovaGrayScaleHash(128);
