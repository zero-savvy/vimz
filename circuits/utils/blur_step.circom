pragma circom 2.0.0;

include "utils/convolution_step.circom";


template Blur(width, kernel_size){
    // public inputs and outputs
    signal input step_in[kernel_size+1];
    // signal input prev_orig_hash_0;
    // signal input prev_orig_hash_1;
    // signal input prev_orig_hash;
    // signal input prev_conv_hash;
    
    signal output step_out[kernel_size+1];
    // signal output next_orig_hash_1;
    // signal output next_orig_hash_2;
    // signal output next_orig_hash;
    // signal output next_conv_hash;
    
    // private inputs
    signal input row_orig [kernel_size][width];
    signal input row_tran [width];

    component integrity_checker = IntegrityCheck(width, kernel_size);
    integrity_checker.step_in <== step_in;
    integrity_checker.row_orig <== row_orig;
    integrity_checker.row_conv <== row_tran;
    step_out <== integrity_checker.step_out;

    component conv_checker = BlurCheck(width, kernel_size);
    conv_checker.row_orig <== row_orig;
    conv_checker.row_conv <== row_tran;
    // conv_checker.kernel <== decompressor_kernel.out;
}

// component main { public [step_in] } = Blur(128, 3);
