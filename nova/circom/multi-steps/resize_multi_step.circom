pragma circom 2.0.0;

include "resize_step.circom";


template ResizeMultiRow(steps, widthOrig, widthResized, rowCountOrig, rowCountResized, actualHeightOrig, actualHeightResized) {
    
    // public inputs
    signal input step_in[2];
    
    // private inputs
    signal input row_orig [steps] [rowCountOrig][widthOrig];
    signal input row_tran [steps] [rowCountResized][widthResized];

    //outputs
    signal output step_out[2];

    component resize[steps];

    for (var i=0; i<steps; i++) { 
        resize[i] = ResizeHash(widthOrig, widthResized, rowCountOrig, rowCountResized, actualHeightOrig, actualHeightResized);
        if (i == 0) {
            resize[i].step_in <== step_in;
        } else {
            resize[i].step_in <== resize[i-1].step_out;
        }
        resize[i].row_orig <== row_orig[i];
        resize[i].row_tran <== row_tran[i];
    }
    step_out <== resize[steps - 1].step_out;
}

component main { public [step_in] } = ResizeMultiRow(2, 128, 64, 3, 2, 720, 480);
