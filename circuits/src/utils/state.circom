pragma circom 2.2.0;

include "hashers.circom";
include "../../node_modules/circomlib/circuits/comparators.circom";

bus IVCState() {
    signal orig_hash;
    signal tran_hash;
}

template UpdateIVCState(width) {
    input IVCState() old;
    signal input row_orig [width];
    signal input row_tran [width];

    output IVCState() new;

    new.orig_hash <== HeadTailHasher(width)(old.orig_hash, row_orig);
    new.tran_hash <== HeadTailHasher(width)(old.tran_hash, row_tran);
}

bus IVCStateWithFactor() {
    IVCState() base;
    signal     factor;
}

template UpdateIVCStateWithFactor(width) {
    input IVCStateWithFactor() old;
    signal input row_orig [width];
    signal input row_tran [width];

    output IVCStateWithFactor() new;

    new.base   <== UpdateIVCState(width)(old.base, row_orig, row_tran);
    new.factor <== old.factor;
}

bus IVCStateConv(kernel_size) {
    IVCState() base;
    signal     common_row_hash [kernel_size - 1];
}

template UpdateIVCStateConv(kernel_size, width) {
    input IVCStateConv(kernel_size) old;
    signal input row_orig [kernel_size][width];
    signal input row_tran [width];

    output IVCStateConv(kernel_size) new;

    signal row_hash[kernel_size];
    for (var i = 0; i < kernel_size; i++) {
        row_hash[i] <== ArrayHasher(width)(row_orig[i]);
    }

    signal fresh_hash[kernel_size - 1];
    for (var i = 0; i < kernel_size - 1; i++) {
        fresh_hash[i] <== IsZero()(old.common_row_hash[i]);
        old.common_row_hash[i] === row_hash[i] * (1 - fresh_hash[i]);
    }

    new.base.orig_hash <== PairHasher()(old.base.orig_hash, row_hash[kernel_size \ 2]);
    new.base.tran_hash <== HeadTailHasher(width)(old.base.tran_hash, row_tran);

    for (var i = 1; i < kernel_size; i++) {
        new.common_row_hash[i-1] <== row_hash[i];
    }
}
