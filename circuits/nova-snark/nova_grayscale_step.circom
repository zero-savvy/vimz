pragma circom 2.0.0;

include "../src/grayscale_step.circom";


template NovaGrayScaleHash(width){
    signal input step_in[2];
    // signal input prev_orig_hash;
    // signal input prev_gray_hash;
    // grayscale factor
    signal output step_out[2];
    // signal output next_orig_hash;
    // signal output next_gray_hash;
    // btightness factor
    
    // Private inputs
    signal input row_orig [width];
    signal input row_tran [width];
    
    component grayscale_circuit = GrayScaleHash(width);
    grayscale_circuit.step_in <== step_in;
    grayscale_circuit.row_orig <== row_orig;
    grayscale_circuit.row_tran <== row_tran;
    grayscale_circuit.step_out ==> step_out;
}

component main { public [step_in] } = NovaGrayScaleHash(128);
