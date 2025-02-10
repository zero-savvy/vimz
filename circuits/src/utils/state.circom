pragma circom 2.2.0;

include "hashers.circom";

bus IVCState() {
    signal orig_hash;
    signal tran_hash;
}

template UpdateIVCState(width){
    input IVCState() old;
    signal input row_orig [width];
    signal input row_tran [width];

    output IVCState() new;

    new.orig_hash <== HeadTailHasher(width)(old.orig_hash, row_orig);
    new.tran_hash <== HeadTailHasher(width)(old.tran_hash, row_tran);
}

bus IVCStateExtended() {
    IVCState() base;
    signal     factor;
}

template UpdateIVCStateExtended(width){
    input IVCStateExtended() old;
    signal input row_orig [width];
    signal input row_tran [width];

    output IVCStateExtended() new;

    new.base   <== UpdateIVCState(width)(old.base, row_orig, row_tran);
    new.factor <== old.factor;
}
