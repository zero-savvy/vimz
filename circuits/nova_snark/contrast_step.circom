pragma circom 2.2.0;

include "../src/contrast_step.circom";

// NovaSnark wrapper over `ContrastHash` circuit.
template NovaContrast(width){
    // ---- Running IVC state ----
    signal input  step_in[3];
    signal output step_out[3];
    // ---- Step inputs ----
    signal input  row_orig[width], row_tran[width];
    // ---- Step computation ----
    step_out <== ContrastHash(width)(step_in, row_orig, row_tran);
}

component main { public [step_in] } = NovaContrast(128);
