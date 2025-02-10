pragma circom 2.2.0;

include "utils/hashers.circom";
include "utils/pixels.circom";
include "../node_modules/circomlib/circuits/bitify.circom";

template BrightnessHash(width){
    input  IVCStateWithFactor() step_in;
    output IVCStateWithFactor() step_out;

    // Private inputs
    signal input row_orig [width];
    signal input row_tran [width];

    // Execute the step
    Brightness(width)(row_orig, row_tran, step_in.factor);
    // Update IVC state
    step_out <== UpdateIVCStateWithFactor(width)(step_in, row_orig, row_tran);
}

template Brightness(width){
    signal input original[width];
    signal input transformed[width];
    signal input bf;

    component decompressor[width];
    component decompressor_brightness[width];
    component brightnesschecker[width];

    for (var j=0; j<width; j++) {
        decompressor[j] = Decompressor();
        decompressor[j].in <== original[j];

        decompressor_brightness[j] = Decompressor();
        decompressor_brightness[j].in <== transformed[j];

        brightnesschecker[j] = BrightnessChecker(10);

        brightnesschecker[j].orig <== decompressor[j].out;
        brightnesschecker[j].bright <== decompressor_brightness[j].out;
        brightnesschecker[j].bf <== bf;
    }

}

template BrightnessChecker(n) {
    signal input orig[n][3];
    signal input bright[n][3];
    signal input bf;
    // signal input brightness_factor;

    signal output n_check;

    component lt[n][3][4];
    component selector[n][3];
    component gt_selector[n][3];

    for (var i = 0; i < n; i++) {      
        var r = bf * orig[i][0];
        var g = bf * orig[i][1];
        var b = bf * orig[i][2];

        var calced[3];
        calced[0] = r;
        calced[1] = g;
        calced[2] = b;

        // log("ORIG:", orig[i][0], orig[i][1], orig[i][2]);
        // log("trans:", bright[i][0], bright[i][1], bright[i][2]);
        // log("calced:", r, g, b);
        // log("--------------------------------");

        for (var color = 0; color < 3; color++) {

            // find sign of r_adjusted
            lt[i][color][0] = LessEqThan(13);
            lt[i][color][1] = LessEqThan(13);
            lt[i][color][0].in[1] <== 0 - calced[color];
            lt[i][color][0].in[0] <==  calced[color];
            lt[i][color][1].in[0] <== 2550;
            lt[i][color][1].in[1] <==  calced[color];
            
            gt_selector[i][color] = Mux1();
            gt_selector[i][color].c[1] <== 2550;
            gt_selector[i][color].c[0] <== calced[color];
            gt_selector[i][color].s <== lt[i][color][1].out;


            selector[i][color] = Mux1();
            selector[i][color].c[0] <== gt_selector[i][color].out;
            selector[i][color].c[1] <== 0;
            selector[i][color].s <== lt[i][color][0].out;

            var final_value = selector[i][color].out;
            // log("final_value:" , final_value);
            lt[i][color][2] = LessEqThan(13);
            lt[i][color][3] = LessEqThan(13);

            lt[i][color][2].in[1] <== 10;
            lt[i][color][2].in[0] <== final_value - 10 * bright[i][color];
            lt[i][color][2].out === 1;

            lt[i][color][3].in[1] <== 10;
            lt[i][color][3].in[0] <== 10 * bright[i][color] - final_value;
            lt[i][color][3].out === 1; 
        }
    }

    n_check <== n;
}
