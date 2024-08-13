pragma circom 2.0.0;

include "node_modules/circomlib/circuits/multiplexer.circom";
include "node_modules/circomlib/circuits/mux1.circom";
include "node_modules/circomlib/circuits/comparators.circom";
include "utils/pixels.circom";
include "utils/row_hasher.circom";


template RedactionHash(block_size){
    // public inputs
    signal input step_in[2];   // inputs: previous_original_hash, previous_transformed_hash
    
    // private inputs
    signal input block_orig [block_size];    // block data
    signal input hide;         // hide_the_block (0: Yes, 1:No)
    
    //outputs
    signal output step_out[2];     // outputs: next_original_hash, next_transformed_hash
    
    // signal decompressed_row_orig [block_size * 10];

    // Decode input Signals
    var prev_orig_hash = step_in[0];
    var prev_redact_hash = step_in[1];
    // var compressed_info = step_in[2];

    // encoding signals
    var next_orig_hash;
    var next_redact_hash;

    component orig_row_hasher = RowHasher(block_size);
    component orig_hasher = Hasher(2);
    component black_row_hasher = RowHasher(block_size);
    component trans_hasher = Hasher(2);


    // compute next original hash
    orig_row_hasher.img <== block_orig;
    orig_hasher.values[0] <== prev_orig_hash;
    orig_hasher.values[1] <== orig_row_hasher.hash;
    next_orig_hash = orig_hasher.hash;

    // assign black block values
    for(var i=0; i< block_size; i++){
        black_row_hasher.img[i] <== 0;
    }

    component select_redact = Mux1();
    select_redact.c[0] <== orig_row_hasher.hash;    // hash of the original block
    select_redact.c[1] <== black_row_hasher.hash;         // redaction of the block

    select_redact.s <== hide;       // selection signal

    trans_hasher.values[0] <== prev_redact_hash;
    trans_hasher.values[1] <== select_redact.out;
    next_redact_hash = trans_hasher.hash;

    step_out[0] <== next_orig_hash;
    step_out[1] <== next_redact_hash;

    
}

component main { public [step_in] } = RedactionHash(10);
