pragma circom 2.0.0;

include "utils/row_hasher.circom";
include "utils/pixels.circom";
include "../node_modules/circomlib/circuits/bitify.circom";
include "../node_modules/circomlib/circuits/multiplexer.circom";
include "../node_modules/circomlib/circuits/mux1.circom";
include "../node_modules/circomlib/circuits/comparators.circom";


template ContrastChecker(n) {
    signal input orig[n][3];
    signal input contrast[n][3];
    signal input cf;      // signal input contrast_factor;

    signal output n_check;
 
    component lt[n][3][4];
    component selector[n][3];
    component gt_selector[n][3];

    for (var color = 0; color < 3; color++) {      
        for (var i = 0; i < n; i++) {      
            var adjusted = ((orig[i][color]) - 128) * cf + 1280;
                    
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

template ContrastHash(width){
    signal input step_in[3];
    // signal input prev_orig_hash;
    // signal input prev_gray_hash;
    // contrast factor
    signal output step_out[3];
    // signal output next_orig_hash;
    // signal output next_gray_hash;
    // contrast factor

    // Private inputs
    signal input row_orig [width];
    signal input row_tran [width];
    
    component orig_row_hasher = RowHasher(width);
    component contrast_row_hasher = RowHasher(width);
    component orig_hasher = Hasher(2);
    component contrast_hasher = Hasher(2);

    orig_row_hasher.img <== row_orig;
    orig_hasher.values[0] <== step_in[0]; // prev_orig_hash
    orig_hasher.values[1] <== orig_row_hasher.hash;
    step_out[0] <== orig_hasher.hash; // next_orig_hash

    contrast_row_hasher.img <== row_tran;
    contrast_hasher.values[0] <== step_in[1]; // prev_contrast_hash
    contrast_hasher.values[1] <== contrast_row_hasher.hash;
    step_out[1] <== contrast_hasher.hash; // next_contrast_hash
    
    step_out[2] <== step_in[2];
    
    // contrast code here ...
    component checker = Contrast(width);
    checker.original <== row_orig;
    checker.transformed <== row_tran;
    checker.cf <== step_in[2];
}

// component main { public [step_in] } = ContrastHash(128);



