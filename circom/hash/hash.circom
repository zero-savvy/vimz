pragma circom 2.0.0;
include "../circomlib/circuits/poseidon.circom";

// Prove being a member of a valid Merkle tree
template Hasher(inputSize) {
    signal input values[inputSize];
    signal output hash;

    component hasher = Poseidon(inputSize);
    for (var i = 0; i < inputSize; i++) {
        hasher.inputs[i] <== values[i];
    }
    hash <== hasher.out;
}

// component main {public [hash]} = Attest(20);
