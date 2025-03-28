pragma circom 2.2.0;

include "../src/crop_step.circom";
include "../src/utils/input_transformation.circom";
include "../src/utils/state.circom";

// Sonobe wrapper over `CropHash` circuit.
template SonobeCrop(widthOrig, widthCrop, heightCrop){
    // ---- Running IVC state ----
    input  IVCStateWithInfo ivc_input;
    output IVCStateWithInfo ivc_output;
    // ---- Step inputs ----
    signal input  external_inputs[widthOrig];
    // ---- Step computation ----
    ivc_output <== CropHash(widthOrig, widthCrop, heightCrop)(ivc_input, external_inputs);
}

component main { public [ivc_input] } = SonobeCrop(128, 64, 480);
