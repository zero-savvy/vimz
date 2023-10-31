pragma circom 2.0.0;
include "../circomlib/circuits/bitify.circom";

template Decompressor(){
    signal input in;
	signal output out[10][3];

	component toBits = Num2Bits(240);
	component toNum[10][3];

	toBits.in <== in;

	for (var i=0; i<10; i++) {
		for (var j=0; j<3; j++) {
			toNum[i][j] = Bits2Num(8);
			toNum[i][j].in[0] <== toBits.out[i*24+j*8];
			toNum[i][j].in[1] <== toBits.out[i*24+j*8+1];
			toNum[i][j].in[2] <== toBits.out[i*24+j*8+2];
			toNum[i][j].in[3] <== toBits.out[i*24+j*8+3];
			toNum[i][j].in[4] <== toBits.out[i*24+j*8+4];
			toNum[i][j].in[5] <== toBits.out[i*24+j*8+5];
			toNum[i][j].in[6] <== toBits.out[i*24+j*8+6];
			toNum[i][j].in[7] <== toBits.out[i*24+j*8+7];
			out[i][j] <== toNum[i][j].out;
		}
	}
}


template DecompressorGrey(){
    signal input in;
	signal output out[10];

	component toBits = Num2Bits(240);
	component toNum[10];

	toBits.in <== in;

	for (var i=0; i<10; i++) {
		var j=0;
		toNum[i] = Bits2Num(8);
		toNum[i].in[0] <== toBits.out[i*24];
		toNum[i].in[1] <== toBits.out[i*24+1];
		toNum[i].in[2] <== toBits.out[i*24+2];
		toNum[i].in[3] <== toBits.out[i*24+3];
		toNum[i].in[4] <== toBits.out[i*24+4];
		toNum[i].in[5] <== toBits.out[i*24+5];
		toNum[i].in[6] <== toBits.out[i*24+6];
		toNum[i].in[7] <== toBits.out[i*24+7];
		out[i] <== toNum[i].out;
	}
}


template CompressorCrop(){
    signal input in[10];
	signal output out;

	component toNum = Bits2Num(240);
	component toBits[10];

	for (var i=0; i<10; i++) {
		toBits[i] = Num2Bits(24);
		toBits[i].in <== in[i];
		for (var j=0; j<24; j++) {
			toNum.in[i*24+j] <== toBits[i].out[j];
		}
	}
	out <== toNum.out;
}

template DecompressorCrop(){
    signal input in;
	signal output out[10];

	component decomp = DecompressorGrey();
	
	decomp.in <== in;
	out <== decomp.out;
}



template Test () {
	signal input sig1;
	signal input sig2;

	component decom = Decompressor();
	decom.in <== sig1;
	sig2 === decom.out[2][2];
}

// component main = Test();