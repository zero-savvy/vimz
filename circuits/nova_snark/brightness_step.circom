pragma circom 2.1.0;

include "../src/brightness_step.circom";

// NovaSnark wrapper over `BrightnessHash` circuit.
template NovaBrightness(width){
    // ---- Running IVC state ----
    signal input  step_in[3];
    signal output step_out[3];
    // ---- Step inputs ----
    signal input  row_orig[width], row_tran[width];
    // ---- Step computation ----
    step_out <== BrightnessHash(width)(step_in, row_orig, row_tran);
}

component main { public [step_in] } = NovaBrightness(128);
