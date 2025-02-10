pragma circom 2.2.0;

include "../src/crop_step.circom";
include "../src/utils/state.circom";

// NovaSnark wrapper over `CropHash` circuit.
template NovaCrop(widthOrig, widthCrop, heightCrop){
    // ---- Running IVC state ----
    input  IVCStateWithInfo step_in;
    output IVCStateWithInfo step_out;
    // ---- Step inputs ----
    signal input row_orig[widthOrig];
    // ---- Step computation ----
    step_out <== CropHash(widthOrig, widthCrop, heightCrop)(step_in, row_orig);
}

component main { public [step_in] } = NovaCrop(128, 64, 480);
