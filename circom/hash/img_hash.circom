pragma circom 2.0.0;
include "hash.circom";

template MerkleTree3 () {
    signal input leaves[2**3];
    signal output root;

    component nodes2 [2**2];
    component nodes1 [2**1];
    component nodes0;

    for(var i=0; i < 2**2; i++) {
        nodes2[i] = Hasher(2);
        nodes2[i].values[0] <== leaves[i*2];
        nodes2[i].values[1] <== leaves[i*2+1];
    }

    for(var i=0; i < 2**1; i++) {
        nodes1[i] = Hasher(2);
        nodes1[i].values[0] <== nodes2[i*2].hash;
        nodes1[i].values[1] <== nodes2[i*2+1].hash;
    }

    nodes0 = Hasher(2);
    nodes0.values[0] <== nodes1[0].hash;
    nodes0.values[1] <== nodes1[1].hash;
    root <== nodes0.hash;

}


template MerkleTree4 () {
    signal input leaves[2**4];
    signal output root;

    component nodes3 [2**3];
    component mt3 = MerkleTree3();

    for(var i=0; i < 2**3; i++) {
        nodes3[i] = Hasher(2);
        nodes3[i].values[0] <== leaves[i*2];
        nodes3[i].values[1] <== leaves[i*2+1];

        mt3.leaves[i] <== nodes3[i].hash;
    }

    root <== mt3.root;
}

template MerkleTree5 () {
    signal input leaves[2**5];
    signal output root;

    component nodes4 [2**4];
    component mt4 = MerkleTree4();

    for(var i=0; i < 2**4; i++) {
        nodes4[i] = Hasher(2);
        nodes4[i].values[0] <== leaves[i*2];
        nodes4[i].values[1] <== leaves[i*2+1];

        mt4.leaves[i] <== nodes4[i].hash;
    }

    root <== mt4.root;
}

template MerkleTree6 () {
    signal input leaves[2**6];
    signal output root;

    component nodes5 [2**5];
    component mt5 = MerkleTree5();

    for(var i=0; i < 2**5; i++) {
        nodes5[i] = Hasher(2);
        nodes5[i].values[0] <== leaves[i*2];
        nodes5[i].values[1] <== leaves[i*2+1];

        mt5.leaves[i] <== nodes5[i].hash;
    }

    root <== mt5.root;
}

template MerkleTree7 () {
    signal input leaves[2**7];
    signal output root;

    component nodes6 [2**6];
    component mt6 = MerkleTree6();

    for(var i=0; i < 2**6; i++) {
        nodes6[i] = Hasher(2);
        nodes6[i].values[0] <== leaves[i*2];
        nodes6[i].values[1] <== leaves[i*2+1];

        mt6.leaves[i] <== nodes6[i].hash;
    }

    root <== mt6.root;
}

template SDhasher () {
    signal input img[480][64];
    signal output hash;

    // For rows
    component rows[480];
    // For columns
    component inner1[240];
    component inner2[120];
    component inner3[60];
    component inner4[30];
    component inner5[15];
    component inner6[7]; // + 1 from lower level
    component mt3 = MerkleTree3();
    
    for(var i=0; i < 480; i++) {
        rows[i] = MerkleTree6();
        rows[i].leaves <== img[i];
    }

    for(var i=0; i < 240; i++) {
        inner1[i] = Hasher(2);
        inner1[i].values[0] <== rows[i*2].root;
        inner1[i].values[1] <== rows[i*2+1].root;
    }

    for(var i=0; i < 120; i++) {
        inner2[i] = Hasher(2);
        inner2[i].values[0] <== inner1[i*2].hash;
        inner2[i].values[1] <== inner1[i*2+1].hash;
    }


    for(var i=0; i < 60; i++) {
        inner3[i] = Hasher(2);
        inner3[i].values[0] <== inner2[i*2].hash;
        inner3[i].values[1] <== inner2[i*2+1].hash;
    }


    for(var i=0; i < 30; i++) {
        inner4[i] = Hasher(2);
        inner4[i].values[0] <== inner3[i*2].hash;
        inner4[i].values[1] <== inner3[i*2+1].hash;
    }


    for(var i=0; i < 15; i++) {
        inner5[i] = Hasher(2);
        inner5[i].values[0] <== inner4[i*2].hash;
        inner5[i].values[1] <== inner4[i*2+1].hash;
    }

    for(var i=0; i < 7; i++) {
        inner6[i] = Hasher(2);
        inner6[i].values[0] <== inner5[i*2].hash;
        inner6[i].values[1] <== inner5[i*2+1].hash;
    }

    for(var i=0; i < 7; i++) {
        mt3.leaves[i] <== inner6[i].hash;
    }
    mt3.leaves[7] <== 0;

    hash <== mt3.root;
}


template HDhasher () {
    signal input img[720][128];
    signal output hash;

    // For rows
    component rows[720];
    // For columns
    component inner1[360];
    component inner2[180];
    component inner3[90];
    component inner4[45];
    component inner5[22]; // + 1 from lower level
    component inner6[11]; // + 1 from lower level
    component inner7[6];
    component inner8[3];
    component inner9; // + 1 from lower level
    component inner10;

    for(var i=0; i < 720; i++) {
        rows[i] = MerkleTree7();
        rows[i].leaves <== img[i];
    }

    for(var i=0; i < 360; i++) {
        inner1[i] = Hasher(2);
        inner1[i].values[0] <== rows[i*2].root;
        inner1[i].values[1] <== rows[i*2+1].root;
    }

    for(var i=0; i < 180; i++) {
        inner2[i] = Hasher(2);
        inner2[i].values[0] <== inner1[i*2].hash;
        inner2[i].values[1] <== inner1[i*2+1].hash;
    }

    for(var i=0; i < 90; i++) {
        inner3[i] = Hasher(2);
        inner3[i].values[0] <== inner2[i*2].hash;
        inner3[i].values[1] <== inner2[i*2+1].hash;
    }

    for(var i=0; i < 45; i++) {
        inner4[i] = Hasher(2);
        inner4[i].values[0] <== inner3[i*2].hash;
        inner4[i].values[1] <== inner3[i*2+1].hash;
    }

    for(var i=0; i < 22; i++) {
        inner5[i] = Hasher(2);
        inner5[i].values[0] <== inner4[i*2].hash;
        inner5[i].values[1] <== inner4[i*2+1].hash;
    }

    for(var i=0; i < 11; i++) {
        inner6[i] = Hasher(2);
        inner6[i].values[0] <== inner5[i*2].hash;
        inner6[i].values[1] <== inner5[i*2+1].hash;
    }

    for(var i=0; i < 5; i++) {
        inner7[i] = Hasher(2);
        inner7[i].values[0] <== inner6[i*2].hash;
        inner7[i].values[1] <== inner6[i*2+1].hash;
    }

    inner7[5] = Hasher(2);
    inner7[5].values[0] <== inner6[11].hash;
    inner7[5].values[1] <== inner4[44].hash;

    for(var i=0; i < 3; i++) {
        inner8[i] = Hasher(2);
        inner8[i].values[0] <== inner7[i*2].hash;
        inner8[i].values[1] <== inner7[i*2+1].hash;
    }

    inner9 = Hasher(2);
    inner9.values[0] <== inner8[0].hash;
    inner9.values[1] <== inner8[1].hash;

    inner10 = Hasher(2);
    inner10.values[0] <== inner8[3].hash;
    inner10.values[1] <== inner9.hash;

    hash <== inner10.hash;
}

// template FHDhasher () {
//     signal input img[1080][192];
//     signal output hash;

//     // For rows
//     component rows1[1080][96];
//     component rows2[1080][48];
//     component rows3[1080][24];
//     component rows4[1080][12];
//     component rows5[1080][6];
//     component rows6[1080][3];
//     component rows7[1080];
//     component rows8[1080];
//     // For columns
//     component inner1[360];
//     component inner2[180];
//     component inner3[90];
//     component inner4[45];
//     component inner5[22]; // + 1 from lower level
//     component inner6[11]; // + 1 from lower level
//     component inner7[6];
//     component inner8[3];
//     component inner9; // + 1 from lower level
//     component inner10;

//     for(var i=0; i < 720; i++) {
//         rows[i] = MerkleTree7();
//         rows[i].leaves <== img[i];
//     }

//     for(var i=0; i < 360; i++) {
//         inner1[i] = Hasher(2);
//         inner1[i].values[0] <== rows[i*2].root;
//         inner1[i].values[1] <== rows[i*2+1].root;
//     }

//     for(var i=0; i < 180; i++) {
//         inner2[i] = Hasher(2);
//         inner2[i].values[0] <== inner1[i*2].hash;
//         inner2[i].values[1] <== inner1[i*2+1].hash;
//     }

//     for(var i=0; i < 90; i++) {
//         inner3[i] = Hasher(2);
//         inner3[i].values[0] <== inner2[i*2].hash;
//         inner3[i].values[1] <== inner2[i*2+1].hash;
//     }

//     for(var i=0; i < 45; i++) {
//         inner4[i] = Hasher(2);
//         inner4[i].values[0] <== inner3[i*2].hash;
//         inner4[i].values[1] <== inner3[i*2+1].hash;
//     }

//     for(var i=0; i < 22; i++) {
//         inner5[i] = Hasher(2);
//         inner5[i].values[0] <== inner4[i*2].hash;
//         inner5[i].values[1] <== inner4[i*2+1].hash;
//     }

//     for(var i=0; i < 11; i++) {
//         inner6[i] = Hasher(2);
//         inner6[i].values[0] <== inner5[i*2].hash;
//         inner6[i].values[1] <== inner5[i*2+1].hash;
//     }

//     for(var i=0; i < 5; i++) {
//         inner7[i] = Hasher(2);
//         inner7[i].values[0] <== inner6[i*2].hash;
//         inner7[i].values[1] <== inner6[i*2+1].hash;
//     }

//     inner7[5] = Hasher(2);
//     inner7[5].values[0] <== inner6[11].hash;
//     inner7[5].values[1] <== inner4[44].hash;

//     for(var i=0; i < 3; i++) {
//         inner8[i] = Hasher(2);
//         inner8[i].values[0] <== inner7[i*2].hash;
//         inner8[i].values[1] <== inner7[i*2+1].hash;
//     }

//     inner9 = Hasher(2);
//     inner9.values[0] <== inner8[0].hash;
//     inner9.values[1] <== inner8[1].hash;

//     inner10 = Hasher(2);
//     inner10.values[0] <== inner8[3].hash;
//     inner10.values[1] <== inner9.hash;

//     hash <== inner10.hash;
// }

template EasyImgHasher (height, width) {
    signal input img[height][width];
    signal output hash;

    // For rows
    component hasher[height*width];

    hasher[1] = Hasher(2);
    hasher[1].values[0] <== img[0][0];
    hasher[1].values[1] <== img[0][1];

    for(var i=0; i < height; i++) {
        for(var j=0; j<width; j++) {
            if (i == 0 && (j == 0 || j ==1)) {
                // do nothing
            } else {
                hasher[i*width+j] = Hasher(2);
                hasher[i*width+j].values[0] <== hasher[i*width+j-1].hash;
                hasher[i*width+j].values[1] <== img[i][j];
            }
        }
    }

    hash <== hasher[height*width-1].hash;

}
component main = EasyImgHasher(480, 30);