// Mini-library exposing various hasher templates. They impement Poseidon hashing for different input types.

pragma circom 2.2.0;
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
template ArrayHasher(LENGTH) {
    signal input  array[LENGTH];
    signal output hash;
    hash <== _WindowFoldHasher(LENGTH, 8)(array);
}

// Compute Poseidon hash of an array by folding the it *one element at a time*.
template _LinearFoldHasher(LENGTH) {
    signal input  array[LENGTH];
    signal output hash;

    signal intermediate_hash[LENGTH-1];

    intermediate_hash[0] <== PairHasher()(array[0], array[1]);
    for(var i = 1; i < LENGTH-1; i++) {
        intermediate_hash[i] <== PairHasher()(intermediate_hash[i-1], array[i+1]);
    }

    hash <== intermediate_hash[LENGTH-2];
}

// Compute Poseidon hash of an array by folding it with a *window of size `WINDOW_SIZE`*.
template _WindowFoldHasher(LENGTH, WINDOW_SIZE) {
    signal input  array[LENGTH];
    signal output hash;

    var numRounds = (LENGTH + WINDOW_SIZE - 1) \ WINDOW_SIZE;

    signal intermediateHashes[numRounds];

    // Process the first window
    var firstWindowSize = (LENGTH < WINDOW_SIZE) ? LENGTH : WINDOW_SIZE;
    component firstHasher = Poseidon(firstWindowSize);
    for (var i = 0; i < firstWindowSize; i++) {
        firstHasher.inputs[i] <== array[i];
    }
    intermediateHashes[0] <== firstHasher.out;

    // Process subsequent windows
    var processed = firstWindowSize;
    component hashers[numRounds - 1];
    for (var foldRound = 0; foldRound < numRounds - 1; foldRound++) {
        var remaining = LENGTH - processed;
        var currentWindowSize = (remaining < WINDOW_SIZE - 1) ? remaining : WINDOW_SIZE - 1;

        hashers[foldRound] = Poseidon(currentWindowSize + 1);
        hashers[foldRound].inputs[0] <== intermediateHashes[foldRound];
        for (var i = 0; i < currentWindowSize; i++) {
            hashers[foldRound].inputs[i + 1] <== array[processed + i];
        }
        intermediateHashes[foldRound + 1] <== hashers[foldRound].out;
        processed += currentWindowSize;
    }

    hash <== intermediateHashes[numRounds - 1];
}

// Compute Poseidon hash of an array by computing `ARITY`-ary Merkle tree of hashes over it.
template _MerkleHasher(LENGTH, ARITY) {
    signal input  array[LENGTH];
    signal output hash;

    var fullChunks = LENGTH \ ARITY;
    var remainingElements = LENGTH % ARITY;
    var chunks = fullChunks + (remainingElements > 0 ? 1 : 0);

    if (LENGTH == 1) {
        hash <== array[0];
    } else {
        // Hashes of disjoint chunks of length `ARITY` (except possibly the last one, which might be shorter).
        signal chunkOutputs[chunks];

        // Handle full chunks.
        component fullHashers[fullChunks];
        for (var i = 0; i < fullChunks; i++) {
            fullHashers[i] = Poseidon(ARITY);
            for (var j = 0; j < ARITY; j++) {
                fullHashers[i].inputs[j] <== array[i * ARITY + j];
            }
            chunkOutputs[i] <== fullHashers[i].out;
        }

        // Handle remaining elements (if any).
        if (remainingElements > 0) {
            component partialHasher = Poseidon(remainingElements);
            for (var i = 0; i < remainingElements; i++) {
                partialHasher.inputs[i] <== array[fullChunks * ARITY + i];
            }
            chunkOutputs[fullChunks] <== partialHasher.out;
        }

        // Recursively hash the chunk hashes.
        hash <== _MerkleHasher(chunks, ARITY)(chunkOutputs);
    }
}

// Compute Poseidon hash of a single value and an array of values.
template HeadTailHasher(TAIL_LENGTH) {
    signal input  head, tail[TAIL_LENGTH];
    signal output hash;

    hash <== PairHasher()(head, ArrayHasher(TAIL_LENGTH)(tail));
}
