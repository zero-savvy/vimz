pragma circom 2.0.0;


template IsZero() {
     signal input in;
     signal output out;

     signal inv;

     inv <-- in!=0 ? 1/in : 0;
     out <== -in*inv + 1;
     in*out === 0;

}

template CheckBrightness() {
     signal input calcVal;
     signal input actualVal;
     signal input remainder;
     signal input x1;
     signal input x2;
     signal input x3;
     signal input x4;
     signal input x5;
     signal input x6;
     signal output out1;
     signal output out2;
     signal output out3;

     component isZero1 = IsZero();
     isZero1.in <== 4 * (2545 - calcVal) + 1 - x1 - x2 - x3;
     out1 <== (1 - isZero1.out) * (actualVal - 255);

     component isZero2 = IsZero();
     isZero2.in <== 4 * (calcVal - 5) + 1 - x4 - x5 - x6;
     out2 <== (1 - isZero2.out) * actualVal;

     var x = isZero1.out + isZero2.out  - 1;
     var y = 10 * actualVal - calcVal + remainder;
     out3 <== x * y;
}


template Bright(n) {

    signal input orig[n][3];
    signal input new[n][3];
    signal input squares[n][3][6];
   
    signal input positiveRemainder[n][3];
    signal input negativeRemainder[n][3];
    
    signal input alpha;
    signal input posBeta;
    signal input negBeta;

    signal output n_check;

    component checkBright[n][3];
 
    for (var i = 0; i < n; i++) {
	for (var j = 0; j < 3; j++) {
             checkBright[i][j] = CheckBrightness();
             checkBright[i][j].calcVal <==  alpha * orig[i][j] + posBeta - negBeta;
             checkBright[i][j].actualVal <== new[i][j];
             checkBright[i][j].remainder <== positiveRemainder[i][j] - negativeRemainder[i][j];

	     checkBright[i][j].x1 <== squares[i][j][0] * squares[i][j][0];
             checkBright[i][j].x2 <== squares[i][j][1] * squares[i][j][1];
             checkBright[i][j].x3 <== squares[i][j][2] * squares[i][j][2];

             checkBright[i][j].x4 <== squares[i][j][3] * squares[i][j][3];
             checkBright[i][j].x5 <== squares[i][j][4] * squares[i][j][4];
             checkBright[i][j].x6 <== squares[i][j][5] * squares[i][j][5];

             checkBright[i][j].out1 === 0;
             checkBright[i][j].out2 === 0;
             checkBright[i][j].out3 === 0; 
        }
    }

    
     n_check <== n;
}

component main = Bright(2000);
