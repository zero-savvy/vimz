pragma circom 2.2.0;

include "../node_modules/circomlib/circuits/multiplexer.circom";
include "../node_modules/circomlib/circuits/mux1.circom";
include "../node_modules/circomlib/circuits/comparators.circom";
include "utils/pixels.circom";
include "utils/hashers.circom";

template CropHash(widthOrig, widthCrop, heightCrop) {
    input  IVCStateWithInfo() step_in;
    output IVCStateWithInfo() step_out;

    // Private inputs
    signal input row_orig [widthOrig];

    signal decompressed_row_orig [widthOrig * 10];

    var prev_crop_hash = step_in.base.tran_hash;

    component info_decomp = CropInfoDecompressor();
    info_decomp.in <== step_in.info;
    var row_index = info_decomp.row_index;
    var crop_start_x = info_decomp.x;
    var crop_start_y = info_decomp.y;

    // encoding signals
    var next_row_index;
    var same_crop_start_x;
    var same_crop_start_y;

    // ----------------------------
    // calc cropped hash
    // ----------------------------
    component decompressor[widthOrig];

    for (var i=0; i<widthOrig; i++) {
        decompressor[i] = DecompressorCrop();
        decompressor[i].in <== row_orig[i];
        for (var j=0; j<10; j++) {
            decompressed_row_orig[i*10+j] <== decompressor[i].out[j];
        }
    }

    component mux_crop = MultiplexerCrop(widthOrig * 10, widthCrop * 10);
    mux_crop.inp <== decompressed_row_orig;
    mux_crop.sel <== crop_start_x;
    component cropped_data[widthCrop];
    for (var i=0; i<widthCrop; i++) {
        cropped_data[i] = CompressorCrop();
        for (var j=0; j<10; j++) {
            cropped_data[i].in[j] <== mux_crop.out[i*10+j];
        }
    }

    component trans_row_hasher = ArrayHasher(widthCrop);
    for (var i=0; i<widthCrop; i++) {
        trans_row_hasher.array[i] <== cropped_data[i].out;
    }

    component selector = Mux1();
    selector.c[0] <== prev_crop_hash;
    selector.c[1] <== PairHasher()(prev_crop_hash, trans_row_hasher.hash);

    // if the row is within the cropped area
    component gte = GreaterEqThan(12);
    gte.in[0] <== row_index;
    gte.in[1] <== crop_start_y;
    component lt = LessThan(12);
    lt.in[0] <== row_index;
    lt.in[1] <== crop_start_y + heightCrop;

    selector.s <== gte.out * lt.out;

    same_crop_start_x = crop_start_x;
    same_crop_start_y = crop_start_y;

    // Update IVC state
    step_out.base.orig_hash <== HeadTailHasher(widthOrig)(step_in.base.orig_hash, row_orig);
    step_out.base.tran_hash <== selector.out;
    step_out.info           <== step_in.info + 1;
}

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
