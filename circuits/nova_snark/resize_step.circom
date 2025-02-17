pragma circom 2.2.0;

include "../src/resize_step.circom";
include "../src/utils/state.circom";

// NovaSnark wrapper over `ResizeHash` circuit.
template NovaResize(widthOrig, widthResized, rowCountOrig, rowCountResized){
    // ---- Running IVC state ----
    input  IVCState step_in;
    output IVCState step_out;
    // ---- Step inputs ----
    signal input row_orig[rowCountOrig][widthOrig];
    signal input row_tran[rowCountResized][widthResized];
    // ---- Step computation ----
    step_out <== ResizeHash(widthOrig, widthResized, rowCountOrig, rowCountResized)(step_in, row_orig, row_tran);
}

component main { public [step_in] } = NovaResize(128, 64, 3, 2);
