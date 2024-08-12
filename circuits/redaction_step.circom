pragma circom 2.0.0;

include "node_modules/circomlib/circuits/multiplexer.circom";
include "node_modules/circomlib/circuits/mux1.circom";
include "node_modules/circomlib/circuits/comparators.circom";
include "utils/pixels.circom";
include "utils/row_hasher.circom";


template MultiplexerCrop(origSize, cropSize) {
    signal input inp[origSize];
    signal input sel;
    signal output out[cropSize];

    component dec = Decoder(origSize);
    component ep[cropSize];
	var selector[cropSize][origSize];

    for (var h=0; h<cropSize; h++) {
        ep[h] = EscalarProduct(origSize);
    }

    sel ==> dec.inp;

    for (var h=0; h<cropSize; h++) {
		for (var k=0; k<h; k++) {
			selector[h][k] = 0;
		}
		for (var k=0; k<origSize - h; k++) {
        	selector[h][k+h] = dec.out[k];
		}
    }

	for (var h=0; h<cropSize; h++) {
        for (var k=0; k<origSize; k++) {
            inp[k] ==> ep[h].in1[k];
            selector[h][k] ==> ep[h].in2[k];
        }
        ep[h].out ==> out[h];
	}
	dec.success === 1;
}


template RedactionHash(block_size){
    // public inputs
    signal input step_in[2];
    
    // private inputs
    signal input block_orig [block_size];
    signal input hide;
    
    //outputs
    signal output step_out[2];
    
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

    // compute black block hash
    for(var i=0; i< block_size; i++){
        black_row_hasher.img[i] <== 0;
    }

    component selector_redact = Mux1();
    selector_redact.c[0] <== orig_row_hasher.hash;    // hash of the original block
    selector_redact.c[1] <== black_row_hasher.hash;         // redaction of the block

    selector_redact.s <== hide;

    trans_hasher.values[0] <== prev_redact_hash;
    trans_hasher.values[1] <== selector_redact.out;
    next_redact_hash = trans_hasher.hash;

    step_out[0] <== next_orig_hash;
    step_out[1] <== next_redact_hash;

    
}

component main { public [step_in] } = RedactionHash(10);
