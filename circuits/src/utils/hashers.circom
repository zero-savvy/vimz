pragma circom 2.0.0;
include "../../node_modules/circomlib/circuits/poseidon.circom";

// Compute Poseidon hash of a pair of values.
template PairHasher() {
    signal input a, b;
    signal output hash;

    component hasher = Poseidon(2);
    hasher.inputs[0] <== a;
    hasher.inputs[1] <== b;
    hash <== hasher.out;
}

// Compute Poseidon hash of an array of values.
template ArrayHasher(length) {
    signal input  sequence[length];
    signal output hash;

    // TODO: Implement a more efficient way to hash a sequence of values. Try batching.
    signal intermediate_hash[length-1];

    intermediate_hash[0] <== PairHasher()(sequence[0], sequence[1]);
    for(var i = 1; i < length-1; i++) {
        intermediate_hash[i] <== PairHasher()(intermediate_hash[i-1], sequence[i+1]);
    }

    hash <== intermediate_hash[length-2];
}

// Compute Poseidon hash of a single value and an array of values.
template HeadTailHasher(tailLength) {
    signal input  head, tail[tailLength];
    signal output hash;

    hash <== PairHasher()(head, ArrayHasher(tailLength)(tail));
}
