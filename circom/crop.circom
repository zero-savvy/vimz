pragma circom 2.0.0;

template Crop(hOrig, wOrig, hNew, wNew, hStartNew, wStartNew) {
    signal input original[hOrig][wOrig][3];
    signal input transformed[hNew][wNew][3];
    
    for (var i = 0; i <  hNew; i++) {
		for (var j = 0; j < wNew; j++) {
			for (var k = 0; k < 3; k++) {
				transformed[i][j][k] === original[hStartNew + i][wStartNew + j][k];	
			}		
		}		
	}
}

component main = Crop(2048, 1536, 300, 300, 100, 100);
