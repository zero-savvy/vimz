pragma circom 2.0.0;

include "../src/brightness_step.circom";


template NovaBrightnessHash(width){
    signal input step_in[3];
    // signal input prev_orig_hash;
    // signal input prev_gray_hash;
    // brightness factor
    signal output step_out[3];
    // signal output next_orig_hash;
    // signal output next_gray_hash;
    // btightness factor
    
    // Private inputs
    signal input row_orig [width];
    signal input row_tran [width];
    
    component brightness_circuit = BrightnessHash(width);
    brightness_circuit.step_in <== step_in;
    brightness_circuit.row_orig <== row_orig;
    brightness_circuit.row_tran <== row_tran;
    brightness_circuit.step_out ==> step_out;
}

component main { public [step_in] } = NovaBrightnessHash(128);
