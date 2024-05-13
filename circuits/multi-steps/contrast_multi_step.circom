pragma circom 2.0.0;

include "contrast_step.circom";


template ContrastMultiRow(steps, width) {
    
    // public inputs
    signal input step_in[6];
    
    // private inputs
    signal input row_orig [steps] [width];
    signal input row_tran [steps] [width];
    
    //outputs
    signal output step_out[6];

    component contrast[steps];

    for (var i=0; i<steps; i++) { 
        contrast[i] = ContrastHash(width);
        if (i == 0) {
            contrast[i].step_in <== step_in;
        } else {
            contrast[i].step_in <== contrast[i-1].step_out;
        }
        contrast[i].row_orig <== row_orig[i];
        contrast[i].row_tran <== row_tran[i];
    }
    step_out <== contrast[steps - 1].step_out;
}

component main { public [step_in] } = ContrastMultiRow(4, 128);
