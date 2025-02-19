pragma circom 2.2.0;

include "../node_modules/circomlib/circuits/mux1.circom";
include "utils/pixels.circom";
include "utils/hashers.circom";

template RedactHash(blockSize) {
    input  IVCState() step_in;
    output IVCState() step_out;

    // Private inputs
    signal input row_orig [blockSize];
    signal input redact;

    var prev_redact_hash = step_in.tran_hash;

    component block_hasher = ArrayHasher(blockSize);
    for (var i=0; i<blockSize; i++) {
        block_hasher.array[i] <== row_orig[i];
    }

    component selector = Mux1();
    selector.c[0] <== PairHasher()(prev_redact_hash, block_hasher.hash);
    selector.c[1] <== PairHasher()(prev_redact_hash, 0);
    selector.s <== redact;

    // Update IVC state
    step_out.orig_hash <== PairHasher()(step_in.orig_hash, block_hasher.hash);
    step_out.tran_hash <== selector.out;
}