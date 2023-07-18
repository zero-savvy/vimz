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

// N is the number of bits the input  have.
// The MSF is the sign bit.
template LessEqThan(n) {
    signal input in[2];
    signal output out;

    component lt = LessThan(n);
    lt.in[0] <== in[0];
    lt.in[1] <== in[1]+1;
    lt.out ==> out;
}

template CheckBrightness() {
     signal input calcVal;
     signal input actualVal;
     signal input remainder;
     signal output out1;
     signal output out2;
     signal output out3;

     component lt1 = LessEqThan(13);
     component lt2 = LessEqThan(13);

     lt1.in[0] <== 2545;
     lt1.in[1] <== calcVal;
     out1 <== lt1.out * (actualVal - 255);

     lt2.in[0] <== calcVal;
     lt2.in[1] <== 5;
     out2 <== lt2.out * actualVal;

     var x = 1 - lt1.out - lt2.out;
     var y = 10 * actualVal - calcVal + remainder;
     out3 <== x * y;
}


template Bright(n) {

    signal input orig[n][3];
    signal input new[n][3];
    signal input positiveRemainder[n][3];
    signal input negativeRemainder[n][3];
    signal input alpha;
    signal input posBeta;
    signal input negBeta;
    signal output n_check;

    component checkBright[n][3];

    signal test[n][3];
 
    for (var i = 0; i < n; i++) {
	for (var j = 0; j < 3; j++) {
             checkBright[i][j] = CheckBrightness();
             checkBright[i][j].calcVal <==  alpha * orig[i][j] + posBeta - negBeta;
             checkBright[i][j].actualVal <== new[i][j];
             checkBright[i][j].remainder <== positiveRemainder[i][j] - negativeRemainder[i][j];

             checkBright[i][j].out1 === 0;
             checkBright[i][j].out2 === 0;
             checkBright[i][j].out3 === 0; 
        }
    }
    n_check <== n;
}

component main = Bright(200);
