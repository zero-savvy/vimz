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

// Compute Poseidon hash of an array of values using a chunk size of 8.
template ArrayHasher(length) {
    signal input array[length];
    signal output hash;

    if (length == 1) {
        hash <== array[0];
    } else {
        var chunkSize = 8;

        var fullChunks = length \ chunkSize;
        component fullHashers[fullChunks];
        for (var i = 0; i < fullChunks; i++) {
            fullHashers[i] = Poseidon(chunkSize);
            for (var j = 0; j < chunkSize; j++) {
                fullHashers[i].inputs[j] <== array[i * chunkSize + j];
            }
        }

        if (length % chunkSize == 0) {
            component nextRound = ArrayHasher(fullChunks);
            for (var i = 0; i < fullChunks; i++) {
                nextRound.array[i] <== fullHashers[i].out;
            }
            hash <== nextRound.hash;
        } else {
            component partialHasher = Poseidon(length % chunkSize);
            for (var i = 0; i < length % chunkSize; i++) {
                partialHasher.inputs[i] <== array[fullChunks * chunkSize + i];
            }
            component nextRound = ArrayHasher(fullChunks + 1);
            for (var i = 0; i < fullChunks; i++) {
                nextRound.array[i] <== fullHashers[i].out;
            }
            nextRound.array[fullChunks] <== partialHasher.out;
            hash <== nextRound.hash;
        }
    }
}

// Compute Poseidon hash of a single value and an array of values.
template HeadTailHasher(tailLength) {
    signal input  head, tail[tailLength];
    signal output hash;

    hash <== PairHasher()(head, ArrayHasher(tailLength)(tail));
}
