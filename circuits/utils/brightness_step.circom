pragma circom 2.0.0;

include "utils/row_hasher.circom";
include "utils/pixels.circom";
include "../node_modules/circomlib/circuits/bitify.circom";


template BrightnessChecker(n) {
    signal input orig[n][3];
    signal input bright[n][3];
    signal input bf;
    // signal input btightness_factor;

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

template BrightnessHash(width){
    signal input step_in[3];
    // signal input prev_orig_hash;
    // signal input prev_gray_hash;
    // brightness factor
    signal output step_out[3];
    // signal output next_orig_hash;
    // signal output next_gray_hash;
    // btightness factor
    
    // Private inputs
    signal input row_orig [width];
    signal input row_tran [width];
    
    component orig_row_hasher = RowHasher(width);
    component brightness_row_hasher = RowHasher(width);
    component orig_hasher = Hasher(2);
    component brightness_hasher = Hasher(2);

    orig_row_hasher.img <== row_orig;
    orig_hasher.values[0] <== step_in[0]; // prev_orig_hash
    orig_hasher.values[1] <== orig_row_hasher.hash;
    step_out[0] <== orig_hasher.hash; // next_orig_hash

    brightness_row_hasher.img <== row_tran;
    brightness_hasher.values[0] <== step_in[1]; // prev_gray_hash
    brightness_hasher.values[1] <== brightness_row_hasher.hash;
    step_out[1] <== brightness_hasher.hash; // next_grey_hash

    step_out[2] <== step_in[2];
    
    component checker = Brightness(width);
    checker.original <== row_orig;
    checker.transformed <== row_tran;
    checker.bf <== step_in[2];

}

// component main { public [step_in] } = BrightnessHash(128);



