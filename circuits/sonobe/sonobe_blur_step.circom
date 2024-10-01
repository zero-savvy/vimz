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

    blur_circuit = Blur(width, kernel_size);
    blur_circuit.step_in <== ivc_input;
    blur_circuit.row_orig <== row_orig;
    blur_circuit.row_tran <== row_tran;
    blur_circuit.step_out ==> ivc_output;


    component integrity_checker = IntegrityCheck(width, kernel_size);
    integrity_checker.step_in <== ivc_input;
    integrity_checker.row_orig <== row_orig;
    integrity_checker.row_conv <== row_tran;
    ivc_output <== integrity_checker.step_out;

    component conv_checker = BlurCheck(width, kernel_size);
    conv_checker.row_orig <== row_orig;
    conv_checker.row_conv <== row_tran;
    // conv_checker.kernel <== decompressor_kernel.out;
}

component main { public [ivc_input] } = Blur(128, 3);
