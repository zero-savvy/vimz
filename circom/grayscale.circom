pragma circom 2.0.0;
include "utils/pixels.circom";
include "round.circom";
include "hash/img_hash.circom";


template GreyScale(height, width){
    
    signal input original[height][width];
    signal input transformed[height][width];
    
    component decompressor[height][width];
    component decompressor_grey[height][width];
    component greychecker[height][width];

    for (var i=0; i<height; i++) {
        for (var j=0; j<width; j++) {
            decompressor[i][j] = Decompressor();
            decompressor[i][j].in <== original[i][j];

            decompressor_grey[i][j] = DecompressorGrey();
            decompressor_grey[i][j].in <== transformed[i][j];
            
            greychecker[i][j] = GrayscaleChecker(10);
            greychecker[i][j].orig <== decompressor[i][j].out;
            greychecker[i][j].gray <== decompressor_grey[i][j].out;
        }
    }

}

template GreyScaleWithHash(height, width) {
    
    signal input original[height][width];
    signal input original_hash;
	signal input transformed[height][width];
    signal input transformed_hash;

    component checker = GreyScale(height, width);
    checker.original <== original;
    checker.transformed <== transformed;

    component origHasher = EasyImgHasher(height, width);
    origHasher.img <== original;
    original_hash === origHasher.hash;

    component tranHasher = EasyImgHasher(height, width);
    tranHasher.img <== transformed;
    transformed_hash === tranHasher.hash;

}

// component main = GreyScale(90, 128); // HD/8 image
// component main = GreyScale(60, 64); // SD/8 image

// component main = GreyScaleWithHash(90, 128); // HD/8 image
component main = GreyScaleWithHash(60, 64); // SD/8 image