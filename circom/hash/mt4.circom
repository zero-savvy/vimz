include "hash.circom";

template merkleTree4() {
    signal input values[16];
    signal output root;

    component h[4];

    // H1
    for (var i = 0; i < 4; i++) {
        h[i] = Hasher(4);
        for (var j = 0; j < 4; j++) {
            h[i].values[j] <== values[i*4 + j];
        }
    }

    // H2
    component h2 = Hasher(4);
    for (var i = 0; i < 4; i++) {
        h2.values[i] <== h[i].hash;
    }

    root <== h2.hash;
}

component main = merkleTree4();