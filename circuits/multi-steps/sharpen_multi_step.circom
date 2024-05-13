pragma circom 2.0.0;

include "sharpen_step.circom";


template SharpenMultiRow(steps, width, kernel_size) {
    
    // public inputs and outputs
    signal input step_in[kernel_size+1];
    // signal input prev_orig_hash_0;
    // signal input prev_orig_hash_1;
    // signal input prev_orig_hash_2;
    // signal input prev_orig_hash_3;
    // signal input prev_orig_hash;
    // signal input prev_conv_hash;
    // signal input compressed_kernel;
    
    signal output step_out[kernel_size+1];
    // signal output next_orig_hash_1;
    // signal output next_orig_hash_2;
    // signal output next_orig_hash_3;
    // signal output next_orig_hash_4;
    // signal output next_orig_hash;
    // signal output next_conv_hash;
    // signal output compressed_kernel;
    
    // private inputs
    signal input row_orig [steps] [kernel_size][width];
    signal input row_tran [steps] [width];

    component sharpen[steps];

    for (var i=0; i<steps; i++) { 
        sharpen[i] = Sharpen(width, kernel_size);
        if (i == 0) {
            sharpen[i].step_in <== step_in;
        } else {
            sharpen[i].step_in <== sharpen[i-1].step_out;
        }
        sharpen[i].row_orig <== row_orig[i];
        sharpen[i].row_tran <== row_tran[i];
    }
    step_out <== sharpen[steps - 1].step_out;
}

component main { public [step_in] } = SharpenMultiRow(2, 128, 3);
