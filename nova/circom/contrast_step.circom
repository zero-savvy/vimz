pragma circom 2.0.0;

include "utils/row_hasher.circom";
include "utils/pixels.circom";
include "circomlib/circuits/bitify.circom";
include "circomlib/circuits/multiplexer.circom";
include "circomlib/circuits/mux1.circom";
include "circomlib/circuits/comparators.circom";


template ContrastChecker(n) {
    signal input orig[n][3];
    signal input contrast[n][3];
    signal input cf;      // signal input contrast_factor;
    signal input r_mean;
    signal input g_mean;
    signal input b_mean;


    signal output n_check;
 
    component lt[n][12];
    component selector[n][3];
    component gt_selector[n][3];

    // r_adjusted = ((r_channel - np.mean(r_channel)) * desired_contrast + np.mean(r_channel)).clip(0, 255).astype(np.uint8)
    for (var i = 0; i < n; i++) {      
        var r_adjusted = ((orig[i][0]) - r_mean) * cf + 1000 * r_mean;
        var g_adjusted = ((orig[i][1]) - g_mean) * cf + 1000 * g_mean;
        var b_adjusted = ((orig[i][2]) - b_mean) * cf + 1000 * b_mean;

        log("means: ", r_mean, g_mean, b_mean);
        log("ORIG:", orig[i][0], orig[i][1], orig[i][2]);
        log("trans:", contrast[i][0], contrast[i][1], contrast[i][2]);
        log("calced:", r_adjusted, g_adjusted, b_adjusted);
        log("--------------------------------");

        
        //=========================== red =======================
        lt[i][0] = LessEqThan(32);
        lt[i][1] = LessEqThan(32);

        lt[i][0].in[1] <== 0 - r_adjusted;
        lt[i][0].in[0] <==  r_adjusted;

        lt[i][1].in[1] <== 255000;
        lt[i][1].in[0] <==  r_adjusted;
        
        
        gt_selector[i][0] = Mux1();
        gt_selector[i][0].c[1] <== 255000;
        gt_selector[i][0].c[0] <== r_adjusted;
        gt_selector[i][0].s <== lt[i][1].out;


        selector[i][0] = Mux1();
        selector[i][0].c[0] <== gt_selector[i][0].out;
        selector[i][0].c[1] <== 0;
        selector[i][0].s <== lt[i][0].out;

        var final_r_value = selector[i][0].out;
        log("final_r_value:" , final_r_value);
        lt[i][6] = LessEqThan(32);
        lt[i][7] = LessEqThan(32);

        lt[i][6].in[1] <== 1000;
        lt[i][6].in[0] <==  final_r_value - (1000 * contrast[i][0]);
        lt[i][6].out === 1;

        lt[i][7].in[1] <== 1000;
        lt[i][7].in[0] <== (1000 * contrast[i][0]) - final_r_value;
        lt[i][7].out === 1; 

        //=========================== green ======================
        lt[i][2] = LessEqThan(32);
        lt[i][3] = LessEqThan(32);

        lt[i][2].in[1] <== 0 - g_adjusted;
        lt[i][2].in[0] <==  g_adjusted;

        lt[i][3].in[1] <== 255000;
        lt[i][3].in[0] <==  g_adjusted;
        
        gt_selector[i][1] = Mux1();
        gt_selector[i][1].c[1] <== 255000;
        gt_selector[i][1].c[0] <== g_adjusted;
        gt_selector[i][1].s <== lt[i][3].out;


        selector[i][1] = Mux1();
        selector[i][1].c[0] <== gt_selector[i][1].out;
        selector[i][1].c[1] <== 0;
        selector[i][1].s <== lt[i][2].out;

        var final_g_value = selector[i][1].out;
        lt[i][8] = LessEqThan(32);
        lt[i][9] = LessEqThan(32);

        lt[i][8].in[1] <== 1000;
        lt[i][8].in[0] <==  final_g_value - (1000 * contrast[i][1]);
        lt[i][8].out === 1;

        lt[i][9].in[1] <== 1000;
        lt[i][9].in[0] <== (1000 * contrast[i][1]) - final_g_value;
        lt[i][9].out === 1; 
        //=========================== blue ======================

        lt[i][4] = LessEqThan(32);
        lt[i][5] = LessEqThan(32);

        lt[i][4].in[1] <== 0 - b_adjusted;
        lt[i][4].in[0] <==  b_adjusted;

        lt[i][5].in[1] <== 255000;
        lt[i][5].in[0] <==  b_adjusted;
        
        gt_selector[i][2] = Mux1();
        gt_selector[i][2].c[1] <== 255000;
        gt_selector[i][2].c[0] <== b_adjusted;
        gt_selector[i][2].s <== lt[i][5].out;


        selector[i][2] = Mux1();
        selector[i][2].c[0] <== gt_selector[i][2].out;
        selector[i][2].c[1] <== 0;
        selector[i][2].s <== lt[i][4].out;

        var final_b_value = selector[i][2].out;
        lt[i][10] = LessEqThan(32);
        lt[i][11] = LessEqThan(32);

        lt[i][10].in[1] <== 1000;
        lt[i][10].in[0] <==  final_b_value - (1000 * contrast[i][2]);
        lt[i][10].out === 1;

        lt[i][11].in[1] <== 1000;
        lt[i][11].in[0] <== (1000 * contrast[i][2]) - final_b_value;
        lt[i][11].out === 1; 

    }

    n_check <== n;
}

template Contrast(width){
    
    signal input original[width];
    signal input transformed[width];
    signal input cf;   // contrast factor
    signal input r_mean;
    signal input g_mean;
    signal input b_mean;

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
        contrastchecker[j].r_mean <== r_mean;
        contrastchecker[j].b_mean <== b_mean;
        contrastchecker[j].g_mean <== g_mean;
    }

}

template ContrastHash(width){
    signal input step_in[6];
    // signal input prev_orig_hash;
    // signal input prev_gray_hash;
    // brightness factor
    // r_mean
    // b_mean
    // g_mean
    signal output step_out[6];
    // signal output next_orig_hash;
    // signal output next_gray_hash;
    // btightness factor
    // r_mean
    // b_mean
    // g_mean
    
    // Private inputs
    signal input row_orig [width];
    signal input row_contrast [width];
    
    component orig_row_hasher = RowHasher(width);
    component contrast_row_hasher = RowHasher(width);
    component orig_hasher = Hasher(2);
    component contrast_hasher = Hasher(2);

    orig_row_hasher.img <== row_orig;
    orig_hasher.values[0] <== step_in[0]; // prev_orig_hash
    orig_hasher.values[1] <== orig_row_hasher.hash;
    step_out[0] <== orig_hasher.hash; // next_orig_hash

    contrast_row_hasher.img <== row_contrast;
    contrast_hasher.values[0] <== step_in[1]; // prev_contrast_hash
    contrast_hasher.values[1] <== contrast_row_hasher.hash;
    step_out[1] <== contrast_hasher.hash; // next_contrast_hash
    step_out[2] <== step_in[2];
    // contrast code here ...
    component checker = Contrast(width);
    checker.original <== row_orig;
    checker.transformed <== row_contrast;
    checker.cf <== step_in[2];
    checker.r_mean <== step_in[3];
    checker.g_mean <== step_in[4];
    checker.b_mean <== step_in[5];

}

component main { public [step_in] } = ContrastHash(128);



