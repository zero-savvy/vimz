pragma circom 2.0.0;

include "../src/brightness_step.circom";


template SonobeBrightnessHash(width){
    signal input ivc_input[3];
    // signal input prev_orig_hash;
    // signal input prev_gray_hash;
    // brightness factor
    signal output ivc_output[3];
    // signal output next_orig_hash;
    // signal output next_gray_hash;
    // brightness factor
    
    // Private inputs
    signal input external_inputs [2 * width];

    signal row_orig [width];
    signal row_tran [width];

    for (var i = 0; i < width; i++) {
        row_orig[i] <== external_inputs[i];
        row_tran[i] <== external_inputs[i + width];
    }
    
    component brightness_circuit = BrightnessHash(width);
    brightness_circuit.step_in <== ivc_input;
    brightness_circuit.row_orig <== row_orig;
    brightness_circuit.row_tran <== row_tran;
    brightness_circuit.step_out ==> ivc_output;
}

component main { public [ivc_input] } = SonobeBrightnessHash(128);
