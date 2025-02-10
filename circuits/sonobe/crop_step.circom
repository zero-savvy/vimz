pragma circom 2.2.0;

include "../src/crop_step.circom";
include "../src/utils/input_transformation.circom";

// Sonobe wrapper over `CropHash` circuit.
template SonobeCrop(widthOrig, widthCrop, heightCrop){
    // ---- Running IVC state ----
    signal input  ivc_input[3];
    signal output ivc_output[3];
    // ---- Step inputs ----
    signal input  external_inputs[widthOrig];
    // ---- Step computation ----
    ivc_output <== CropHash(widthOrig, widthCrop, heightCrop)(ivc_input, external_inputs);
}

component main { public [ivc_input] } = SonobeCrop(128, 64, 480);
