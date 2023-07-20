include "hash.circom";

template merkleTree2() {
    signal input values[16];
    signal output root;

    component h[8];
    component h2[4];
    component h3[2];


    // H1
    for (var i = 0; i < 8; i++) {
        h[i] = Hasher(2);
        for (var j = 0; j < 2; j++) {
            h[i].values[j] <== values[i*2 + j];
        }
    }

    // H2
    for (var i = 0; i < 4; i++) {
        h2[i] = Hasher(2);
        for (var j = 0; j < 2; j++) {
            h2[i].values[j] <== h[i*2 + j].hash;
        }
    }

    // H3
    for (var i = 0; i < 2; i++) {
        h3[i] = Hasher(2);
        for (var j = 0; j < 2; j++) {
            h3[i].values[j] <== h[i*2 + j].hash;
        }
    }

    // H3
    component h4 = Hasher(2);
    for (var i = 0; i < 2; i++) {
        h4.values[i] <== h3[i].hash;
    }

    root <== h4.hash;
}

component main = merkleTree2();