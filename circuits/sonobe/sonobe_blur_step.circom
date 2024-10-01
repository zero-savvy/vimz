pragma circom 2.0.0;

include "../src/blur_step.circom";


template SonobeBlur(width, kernel_size){
    // public inputs and outputs
    signal input ivc_input[kernel_size+1];
    // signal input prev_orig_hash_0;
    // signal input prev_orig_hash_1;
    // signal input prev_orig_hash;
    // signal input prev_conv_hash;
    
    signal output ivc_output[kernel_size+1];
    // signal output next_orig_hash_1;
    // signal output next_orig_hash_2;
    // signal output next_orig_hash;
    // signal output next_conv_hash;
    
    // private inputs
    signal input external_inputs [kernel_size * width + width];

    signal row_orig [kernel_size][width];
    signal row_tran [width];

    for (var i = 0; i < width; i++) {
        for (var j = 0; j < kernel_size; j++) {
            row_orig[j][i] <== external_inputs[j * width + i];
        }
        row_tran[i] <== external_inputs[i + kernel_size * width];
    }

    component blur_circuit = Blur(width, kernel_size);
    blur_circuit.step_in <== ivc_input;
    blur_circuit.row_orig <== row_orig;
    blur_circuit.row_tran <== row_tran;
    blur_circuit.step_out ==> ivc_output;

}

component main { public [ivc_input] } = SonobeBlur(128, 3);
