pragma circom 2.1.0;

include "../src/resize_step.circom";

// NovaSnark wrapper over `ResizeHash` circuit.
template NovaResize(widthOrig, widthResized, rowCountOrig, rowCountResized){
    // ---- Running IVC state ----
    signal input  step_in[2];
    signal output step_out[2];
    // ---- Step inputs ----
    signal input row_orig[rowCountOrig][widthOrig];
    signal input row_tran[rowCountResized][widthResized];
    // ---- Step computation ----
    step_out <== ResizeHash(widthOrig, widthResized, rowCountOrig, rowCountResized)(step_in, row_orig, row_tran);
}

component main { public [step_in] } = NovaResize(128, 64, 3, 2);
