pragma circom 2.0.0;
include "circomlib/circuits/bitify.circom";

template GrayscaleChecker(n) {
    signal input orig[n][3];
    signal input gray[n];

    signal output n_check;
 
    component lt[n][2];
//  = LessEqThan(16);
//    component lt2 = LessEqThan(16);

    for (var i = 0; i < n; i++) {      
        var inter = 30 * orig[i][0] + 59 * orig[i][1] + 11 * orig[i][2];

        lt[i][0] = LessEqThan(16);
        lt[i][1] = LessEqThan(16);

        lt[i][0].in[1] <== 100;
        lt[i][0].in[0] <== inter - 100 * gray[i];
        lt[i][0].out === 1;

        lt[i][1].in[1] <== 100;
        lt[i][1].in[0] <== 100 * gray[i] - inter;
        lt[i][1].out === 1; 
    }
    n_check <== n;
}

// component main = GrayscaleChecker(8000);