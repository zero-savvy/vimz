pragma circom 2.0.0;

include "brightness_step.circom";


template BrightnessMultiRow(steps, width) {
    
    signal input step_in[3];
    // signal input prev_orig_hash;
    // signal input prev_gray_hash;
    // brightness factor
    signal output step_out[3];
    // signal output next_orig_hash;
    // signal output next_gray_hash;
    // btightness factor
    
    // private inputs
    signal input row_orig [steps] [width];
    signal input row_tran [steps] [width];

    component brightness[steps];

    for (var i=0; i<steps; i++) { 
        brightness[i] = BrightnessHash(width);
        if (i == 0) {
            brightness[i].step_in <== step_in;
        } else {
            brightness[i].step_in <== brightness[i-1].step_out;
        }
        brightness[i].row_orig <== row_orig[i];
        brightness[i].row_tran <== row_tran[i];
    }
    step_out <== brightness[steps - 1].step_out;
}

component main { public [step_in] } = BrightnessMultiRow(2, 128);
