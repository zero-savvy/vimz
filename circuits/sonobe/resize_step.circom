pragma circom 2.2.0;

include "../src/resize_step.circom";
include "../src/utils/input_transformation.circom";
include "../src/utils/state.circom";

// Sonobe wrapper over `ResizeHash` circuit.
template SonobeResize(widthOrig, widthResized, rowCountOrig, rowCountResized){
    // ---- Running IVC state ----
    input  IVCState ivc_input;
    output IVCState ivc_output;
    // ---- Step inputs ----
    signal input  external_inputs[widthOrig * rowCountOrig + widthResized * rowCountResized];
    // ---- Input transformation ----
    signal row_orig[rowCountOrig][widthOrig];
    signal row_tran[rowCountResized][widthResized];
    (row_orig, row_tran) <== ResizeInput(widthOrig, widthResized, rowCountOrig, rowCountResized)(external_inputs);
    // ---- Step computation ----
    ivc_output <== ResizeHash(widthOrig, widthResized, rowCountOrig, rowCountResized)(ivc_input, row_orig, row_tran);
}

component main { public [ivc_input] } = SonobeResize(128, 64, 3, 2);
