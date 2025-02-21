pragma circom 2.2.0;

include "src/utils/hashers.circom";

// Compute hash for a full image.
template FullImageHash(rowWidth, rows){
    // ---- Image pixels, given row by row. ----
    signal input  image[rows][rowWidth];
    // ---- Resulting hash ----
    signal output hash;

    // ---- Intermediate hash after each row. The initial value is 0. ----
    signal intermediate_hash[rows + 1];
    intermediate_hash[0] <== 0;

    // ---- Accumulate the hash by each row. ----
    for (var i = 0; i < rows; i++) {
        intermediate_hash[i+1] <== HeadTailHasher(rowWidth)(intermediate_hash[i], image[i]);
    }

    // ---- The final hash is the hash of the last row. ----
    hash <== intermediate_hash[rows];
}

// ---- Main component ----
//
// Computes the hash of a full image with 720 rows, each row with 128 'pixels' (actually, a 'pixel' might encode
// multiple real pixels by using some compression).
//
// In VIMz, we compress 10 real pixels into a single field element, and thus this circuit is dedicated for images with
// HD resolution (1280x720).
component main { public [image] } = FullImageHash(128, 720);
