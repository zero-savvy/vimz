pragma circom 2.0.0;

template Num2Bits(n) {
    signal input in;
    signal output out[n];

    var lc1=0;
    var e2=1;

    for (var i = 0; i<n; i++) {
        out[i] <-- (in >> i) & 1;
        out[i] * (out[i] -1 ) === 0;
        lc1 += out[i] * e2;
        e2 = e2+e2;
    }
    lc1 === in;
}

template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.out[n];
}

template LessEqThan(n) {
    signal input in[2];
    signal output out;

    component lt = LessThan(n);

    lt.in[0] <== in[0];
    lt.in[1] <== in[1]+1;

    lt.out ==> out;
}

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

component main = GrayscaleChecker(8000);