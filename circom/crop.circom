pragma circom 2.0.0;
include "circomlib/circuits/multiplexer.circom";

template MultiplexerCrop(wIn, nIn, hOut) {
    signal input inp[nIn][wIn];
    signal input sel;
    signal output out[hOut][wIn];
    component dec = Decoder(nIn);
    component ep[hOut][wIn];
	var selector[hOut][nIn];

    for (var h=0; h<hOut; h++) {
		for (var k=0; k<wIn; k++) {
        	ep[h][k] = EscalarProduct(nIn);
		}
    }

    sel ==> dec.inp;

    for (var h=0; h<hOut; h++) {
		for (var k=0; k<h; k++) {
			selector[h][k] = 0;
		}
		for (var k=0; k<nIn - h; k++) {
        	selector[h][k+h] = dec.out[k];
		}
    }

	for (var h=0; h<hOut; h++) {
		for (var j=0; j<wIn; j++) {
			for (var k=0; k<nIn; k++) {
				inp[k][j] ==> ep[h][j].in1[k];
				selector[h][k] ==> ep[h][j].in2[k];
			}
			ep[h][j].out ==> out[h][j];
		}
	}
	dec.success === 1;
}


template Crop(hOrig, wOrig, hNew, wNew) {
    signal input hash;
	signal input hStartNew;
	signal input wStartNew;
    signal input original[hOrig][wOrig];
    signal input transformed[hNew][wNew];
	signal output check;
	var tmp1;
	var tmp2;
	var tmp [hOrig][wOrig];
	var compare_matrix [hOrig][wOrig];
	var compare_pixel;

	component smartMux;
	component smartMux2;

	smartMux = MultiplexerCrop(wOrig, hOrig, hNew);
	smartMux.inp <== original;
	smartMux.sel <== hStartNew;

	compare_pixel = 423;

	smartMux2 = MultiplexerCrop(hNew, wOrig, wNew);

	for (var i = 0; i <  hNew; i++) {
		for (var j = 0; j < wOrig; j++) {
			smartMux2.inp[j][i] <== smartMux.out[i][j];
		}
	}
	smartMux2.sel <== wStartNew;

	for (var i = 0; i <  hNew; i++) {
		for (var j = 0; j < wNew; j++) {
			transformed[i][j] === smartMux2.out[j][i];
		}
	}
	
	check <== hash * compare_pixel;
	check === hash * 423;
}

component main {public[hash]}= Crop(100, 100, 10, 20);
