pragma circom 2.2.0;

include "../src/crop_step.circom";

// NovaSnark wrapper over `CropHash` circuit.
template NovaCrop(widthOrig, widthCrop, heightCrop){
    // ---- Running IVC state ----
    signal input  step_in[3];
    signal output step_out[3];
    // ---- Step inputs ----
    signal input row_orig[widthOrig];
    // ---- Step computation ----
    step_out <== CropHash(widthOrig, widthCrop, heightCrop)(step_in, row_orig);
}

component main { public [step_in] } = NovaCrop(128, 64, 480);
