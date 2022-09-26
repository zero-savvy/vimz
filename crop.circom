pragma circom 2.0.0;

template Crop(hOrig, wOrig, hNew, wNew, hStartNew, wStartNew) {

    signal input orig[hOrig][wOrig][3];

    signal input new[hNew][wNew][3];

    signal output n_check;


    for (var i = 0; i <  hNew; i++) {

		for (var j = 0; j < wNew; j++) {

			for (var k = 0; k < 3; k++) {
				new[i][j][k] === orig[hStartNew + i][wStartNew + j][k];	
			}		
		}		
	}
	n_check <== 1;

}



component main = Crop(700, 700, 350, 350, 0, 0);
