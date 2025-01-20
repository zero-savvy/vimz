pragma circom 2.0.0;

include "utils/convolution_step.circom";


template Sharpen(width, kernel_size){
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
    signal input row_orig [kernel_size][width];
    signal input row_tran [width];

    component integrity_checker = IntegrityCheck(width, kernel_size);
    integrity_checker.step_in <== step_in;
    integrity_checker.row_orig <== row_orig;
    integrity_checker.row_conv <== row_tran;
    step_out <== integrity_checker.step_out;

    component conv_checker = SharpenCheck(width, kernel_size);
    conv_checker.row_orig <== row_orig;
    conv_checker.row_conv <== row_tran;
}

// component main { public [step_in] } = Sharpen(128, 3);
