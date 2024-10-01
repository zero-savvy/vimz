pragma circom 2.0.0;

include "../src/grayscale_step.circom";


template SonobeGrayScaleHash(width){
    signal input ivc_input[2];
    // signal input prev_orig_hash;
    // signal input prev_gray_hash;
    signal output ivc_output[2];
    // signal output next_orig_hash;
    // signal output next_gray_hash;
    
    // Private inputs
    signal input external_inputs [2 * width];

    signal row_orig [width];
    signal row_tran [width];

    for (var i = 0; i < width; i++) {
        row_orig[i] <== external_inputs[i];
        row_tran[i] <== external_inputs[i + width];
    }

    component grayscale_circuit = GrayScaleHash(width);
    grayscale_circuit.step_in <== ivc_input;
    grayscale_circuit.row_orig <== row_orig;
    grayscale_circuit.row_tran <== row_tran;
    grayscale_circuit.step_out ==> ivc_output;
}

component main { public [ivc_input] } = SonobeGrayScaleHash(128);
