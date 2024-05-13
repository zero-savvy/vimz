pragma circom 2.0.0;

include "grayscale_step.circom";


template GrayScaleMultiRow(steps, width) {
    
    signal input step_in[2];
    // signal input prev_orig_hash;
    // signal input prev_gray_hash;
    signal output step_out[2];
    // signal output next_orig_hash;
    // signal output next_gray_hash;
    
    // private inputs
    signal input row_orig [steps] [width];
    signal input row_tran [steps] [width];

    component grayscale[steps];

    for (var i=0; i<steps; i++) { 
        grayscale[i] = GrayScaleHash(width);
        if (i == 0) {
            grayscale[i].step_in <== step_in;
        } else {
            grayscale[i].step_in <== grayscale[i-1].step_out;
        }
        grayscale[i].row_orig <== row_orig[i];
        grayscale[i].row_tran <== row_tran[i];
    }
    step_out <== grayscale[steps - 1].step_out;
}

component main { public [step_in] } = GrayScaleMultiRow(2, 128);
