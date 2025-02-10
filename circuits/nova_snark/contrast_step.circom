pragma circom 2.2.0;

include "../src/contrast_step.circom";
include "../src/utils/state.circom";

// NovaSnark wrapper over `ContrastHash` circuit.
template NovaContrast(width){
    // ---- Running IVC state ----
    input  IVCStateWithFactor step_in;
    output IVCStateWithFactor step_out;
    // ---- Step inputs ----
    signal input row_orig[width], row_tran[width];
    // ---- Step computation ----
    step_out <== ContrastHash(width)(step_in, row_orig, row_tran);
}

component main { public [step_in] } = NovaContrast(128);
