pragma circom 2.0.0;
include "utils/pixels.circom";
include "round.circom"

template GreyScale(width, height){
    signal input in [width][height];
    signal input in_hash;
	signal input out[width][height];
    signal input out_hash;

    component decompressor[width][height];
    component decompressor_grey[width][height];
    component greychecker[width][height]

    for (var i=0; i<height; i++) {
        for (var j=0; j<width; j++) {
            decompressor[i][j] = Decompressor();
            decompressor[i][j].in <== in[i][j];

            decompressor_grey[i][j] = DecompressorGrey();
            decompressor_grey[i][j].in <== in[i][j];
            
            greychecker[i][j] = GreyscaleChecker(10);
            greychecker[i][j].orig <== decompressor[i][j].out;
            greychecker[i][j].grey <== decompressor_grey[i][j].out;
        }

    }
}
component main = GreyScale(720, 128);