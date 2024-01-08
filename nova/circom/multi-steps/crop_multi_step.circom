pragma circom 2.0.0;

include "crop_step.circom";


template CropMultiRow(steps, widthOrig, widthCrop, heightCrop) {
    
    // public inputs
    signal input step_in[5];
    
    // private inputs
    signal input row_orig [steps] [widthOrig];
    
    //outputs
    signal output step_out[5];

    component crop[steps];

    for (var i=0; i<steps; i++) { 
        crop[i] = CropHash(widthOrig, widthCrop, heightCrop);
        if (i == 0) {
            crop[i].step_in <== step_in;
        } else {
            crop[i].step_in <== crop[i-1].step_out;
        }
        crop[i].row_orig <== row_orig[i];
    }
    step_out <== crop[steps - 1].step_out;
}

component main { public [step_in] } = CropMultiRow(4, 128, 64, 480);
