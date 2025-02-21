pragma circom 2.2.0;

include "src/utils/hashers.circom";

// Hash a row of an image together with the accumulated hash from the previous rows.
//
// `width` is the number of fields element in a single row.
template ImageRunningHash(width){
    // ---- Image row. ----
    signal input row[width];
    // ---- Accumulated hash from the previous rows. ----
    signal input accumulator;
    // ---- Compute resulting hash. ----
    signal output hash <== HeadTailHasher(width)(accumulator, row);
    // ---- Print the hash. ----
    log(hash);
}

component main { public [row, accumulator] } = ImageRunningHash(128);
