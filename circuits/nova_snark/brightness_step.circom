pragma circom 2.2.0;

include "../src/brightness_step.circom";
include "../src/utils/state.circom";

// NovaSnark wrapper over `BrightnessHash` circuit.
template NovaBrightness(width){
    // ---- Running IVC state ----
    input  IVCStateExtended step_in;
    output IVCStateExtended step_out;
    // ---- Step inputs ----
    signal input row_orig[width], row_tran[width];
    // ---- Step computation ----
    step_out <== BrightnessHash(width)(step_in, row_orig, row_tran);
}

component main { public [step_in] } = NovaBrightness(128);
