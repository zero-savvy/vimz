pragma circom 2.0.0;

include "../src/blur_step.circom";


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

    blur_circuit = Blur(width, kernel_size);
    blur_circuit.step_in <== step_in;
    blur_circuit.row_orig <== row_orig;
    blur_circuit.row_tran <== row_tran;
    blur_circuit.step_out ==> step_out;

}

component main { public [step_in] } = Blur(128, 3);