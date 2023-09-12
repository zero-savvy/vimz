pragma circom 2.0.0;
include "../circomlib/circuits/bitify.circom";

template Decompressor (){
    signal input in;
	signal output out[4][3];

	component toBits = Num2Bits(192);
	component toNum[12];

	toBits.in <== in;

	for (var i=0; i<4; i++) {
		for (var j=0; j<3; j++) {
			toNum[i*3+j] = Bits2Num(8);
			toNum[i*3+j].in[0] <== toBits.out[i*24+j*8];
			toNum[i*3+j].in[1] <== toBits.out[i*24+j*8+1];
			toNum[i*3+j].in[2] <== toBits.out[i*24+j*8+2];
			toNum[i*3+j].in[3] <== toBits.out[i*24+j*8+3];
			toNum[i*3+j].in[4] <== toBits.out[i*24+j*8+4];
			toNum[i*3+j].in[5] <== toBits.out[i*24+j*8+5];
			toNum[i*3+j].in[6] <== toBits.out[i*24+j*8+6];
			toNum[i*3+j].in[7] <== toBits.out[i*24+j*8+7];
			out[i][j] <== toNum[i*3+j].out;
		}
	}
}


template Test () {
	signal input sig1;
	signal input sig2;

	component decom = Decompressor();
	decom.in <== sig1;
	sig2 === decom.out[2][2];
}

component main = Test();
