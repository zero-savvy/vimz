pragma circom 2.0.0;

include "../node_modules/circomlib/circuits/multiplexer.circom";
include "../node_modules/circomlib/circuits/mux1.circom";
include "../node_modules/circomlib/circuits/comparators.circom";
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


template CropHash(widthOrig, widthCrop, heightCrop, x, y){
    // public inputs
    signal input step_in[3];
    
    // private inputs
    signal input row_orig [widthOrig];
    
    //outputs
    signal output step_out[3];
    
    var decompressed_row_orig [widthOrig * 10];

    // Decode input Signals
    var prev_orig_hash = step_in[0];
    var prev_crop_hash = step_in[1];
    var row_index = step_in[2];

    // encoding signals
    var next_orig_hash;
    var next_crop_hash;

    component orig_row_hasher = RowHasher(widthOrig);
    component trans_row_hasher = RowHasher(widthCrop);
    component orig_hasher = Hasher(2);
    component trans_hasher = Hasher(2);


    orig_row_hasher.img <== row_orig;
    orig_hasher.values[0] <== prev_orig_hash;
    orig_hasher.values[1] <== orig_row_hasher.hash;
    next_orig_hash = orig_hasher.hash;

    // ----------------------------
    // calc cropped hash
    // ----------------------------
    component decompressor[widthOrig];

    for (var i=0; i<widthOrig; i++) {
        decompressor[i] = DecompressorCrop();
        decompressor[i].in <== row_orig[i];
        for (var j=0; j<10; j++) {
            decompressed_row_orig[i*10+j] = decompressor[i].out[j];
        }
    }

    var uncompressed_crop[widthCrop * 10];
    for (var i=0; i<widthCrop * 10; i++) { 
        uncompressed_crop[i] = decompressed_row_orig[x+i];
    }
    component cropped_data[widthCrop];
    for (var i=0; i<widthCrop; i++) {
        cropped_data[i] = CompressorCrop();
        for (var j=0; j<10; j++) {
            cropped_data[i].in[j] <== uncompressed_crop[i*10+j];
        }
    } 

    for (var i=0; i<widthCrop; i++) {
        trans_row_hasher.img[i] <== cropped_data[i].out;
    }
    trans_hasher.values[0] <== prev_crop_hash;
    trans_hasher.values[1] <== trans_row_hasher.hash;
    
    component selector = Mux1();
    selector.c[0] <== prev_crop_hash;
    selector.c[1] <== trans_hasher.hash;

    // if the row is within the cropped area
    component gte = GreaterEqThan(12);
    gte.in[0] <== row_index;
    gte.in[1] <== y;
    component lt = LessThan(12);
    lt.in[0] <== row_index;
    lt.in[1] <== y + heightCrop;

    selector.s <== gte.out * lt.out;

    next_crop_hash = selector.out;

    step_out[0] <== next_orig_hash;
    step_out[1] <== next_crop_hash;
    step_out[2] <== row_index + 1;

    
}

// component main { public [step_in] } = CropHash(128, 64, 480, 236, 105);
