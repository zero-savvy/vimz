pragma circom 2.0.0;
include "circomlib/circuits/bitify.circom";

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
