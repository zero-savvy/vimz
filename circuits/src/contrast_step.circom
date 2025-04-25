pragma circom 2.2.0;

include "utils/hashers.circom";
include "utils/pixels.circom";
include "../node_modules/circomlib/circuits/bitify.circom";
include "../node_modules/circomlib/circuits/multiplexer.circom";
include "../node_modules/circomlib/circuits/mux1.circom";
include "../node_modules/circomlib/circuits/comparators.circom";

template ContrastHash(width){
    input  IVCStateWithInfo() step_in;
    output IVCStateWithInfo() step_out;

    // Private inputs
    signal input row_orig [width];
    signal input row_tran [width];

    // Execute the step
    Contrast(width)(row_orig, row_tran, step_in.info);
    // Update IVC state
    step_out <== UpdateIVCStateWithInfo(width)(step_in, row_orig, row_tran);
}

template Contrast(width){
    signal input original[width];
    signal input transformed[width];
    signal input cf;   // contrast factor

    component decompressor[width];
    component decompressor_contrast[width];
    component contrastchecker[width];

    for (var j=0; j<width; j++) {
        decompressor[j] = Decompressor();
        decompressor[j].in <== original[j];

        decompressor_contrast[j] = Decompressor();
        decompressor_contrast[j].in <== transformed[j];

        contrastchecker[j] = ContrastChecker(10);

        contrastchecker[j].orig <== decompressor[j].out;
        contrastchecker[j].contrast <== decompressor_contrast[j].out;
        contrastchecker[j].cf <== cf;
    }

}

template ContrastChecker(n) {
    signal input orig[n][3];
    signal input contrast[n][3];
    signal input cf;      // signal input contrast_factor;

    signal output n_check;
 
    component nb[n][3][4];
    component lt[n][3][4];
    component selector[n][3];
    component gt_selector[n][3];

    for (var color = 0; color < 3; color++) {      
        for (var i = 0; i < n; i++) {      
            var adjusted = ((orig[i][color]) - 128) * cf + 1280;
                    
            nb[i][color][0] = Num2Bits(13);
            nb[i][color][1] = Num2Bits(13);
            nb[i][color][0].in <== adjusted;
            nb[i][color][1].in <== 0 - adjusted;

            // find sign of r_adjusted
            lt[i][color][0] = LessEqThan(13);
            lt[i][color][1] = LessEqThan(13);
            lt[i][color][0].in[1] <== 0 - adjusted;
            lt[i][color][0].in[0] <==  adjusted;
            lt[i][color][1].in[0] <== 2550;
            lt[i][color][1].in[1] <==  adjusted;
            
            gt_selector[i][color] = Mux1();
            gt_selector[i][color].c[1] <== 2550;
            gt_selector[i][color].c[0] <== adjusted;
            gt_selector[i][color].s <== lt[i][color][1].out;


            selector[i][color] = Mux1();
            selector[i][color].c[0] <== gt_selector[i][color].out;
            selector[i][color].c[1] <== 0;
            selector[i][color].s <== lt[i][color][0].out;

            var final_value = selector[i][color].out;
            // log("final_value:" , final_value, contrast[i][color]);

            nb[i][color][2] = Num2Bits(13);
            nb[i][color][3] = Num2Bits(13);

            nb[i][color][2].in <== final_value - (10 * contrast[i][color]);
            nb[i][color][3].in <== (10 * contrast[i][color]) - final_value;

            lt[i][color][2] = LessEqThan(13);
            lt[i][color][3] = LessEqThan(13);

            lt[i][color][2].in[1] <== 10;
            lt[i][color][2].in[0] <== final_value - (10 * contrast[i][color]);
            lt[i][color][2].out === 1;

            lt[i][color][3].in[1] <== 10;
            lt[i][color][3].in[0] <== (10 * contrast[i][color]) - final_value;
            lt[i][color][3].out === 1; 
        }
    }

    n_check <== n;
}
