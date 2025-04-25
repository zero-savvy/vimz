pragma circom 2.2.0;

include "utils/hashers.circom";
include "utils/pixels.circom";
include "utils/state.circom";
include "../node_modules/circomlib/circuits/bitify.circom";

template GrayScaleHash(width){
    input  IVCState() step_in;
    output IVCState() step_out;

    // Private inputs
    signal input row_orig [width];
    signal input row_tran [width];

    // Execute the step
    GrayScale(width)(row_orig, row_tran);
    // Update IVC state
    step_out <== UpdateIVCState(width)(step_in, row_orig, row_tran);
}

template GrayScale(width){
    signal input original[width];
    signal input transformed[width];
    
    component decompressor[width];
    component decompressor_gray[width];
    component graychecker[width];

    for (var j=0; j<width; j++) {
        decompressor[j] = Decompressor();
        decompressor[j].in <== original[j];

        decompressor_gray[j] = DecompressorGray();
        decompressor_gray[j].in <== transformed[j];
        
        graychecker[j] = GrayscaleChecker(10);
        graychecker[j].orig <== decompressor[j].out;
        graychecker[j].gray <== decompressor_gray[j].out;
    }
}

template GrayscaleChecker(n) {
    signal input orig[n][3];
    signal input gray[n];

    signal output n_check;
 
    component nb[n][2];
    component lt[n][2];

    for (var i = 0; i < n; i++) {      
        var inter = 299 * orig[i][0] + 587 * orig[i][1] + 114 * orig[i][2];

        nb[i][0] = Num2Bits(18);
        nb[i][1] = Num2Bits(18);

        nb[i][0].in <== inter - 1000 * gray[i];
        nb[i][1].in <== 1000 * gray[i] - inter;

        lt[i][0] = LessEqThan(18);
        lt[i][1] = LessEqThan(18);

        lt[i][0].in[1] <== 1000;
        lt[i][0].in[0] <== inter - 1000 * gray[i];
        lt[i][0].out === 1;

        lt[i][1].in[1] <== 1000;
        lt[i][1].in[0] <== 1000 * gray[i] - inter;
        lt[i][1].out === 1; 
    }
    n_check <== n;
}
