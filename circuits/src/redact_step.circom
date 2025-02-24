pragma circom 2.2.0;

include "../node_modules/circomlib/circuits/mux1.circom";
include "utils/pixels.circom";
include "utils/hashers.circom";

template RedactHash(blockSize) {
    input  IVCState() step_in;
    output IVCState() step_out;

    // Private inputs
    signal input block [blockSize];
    signal input redact;

    signal prev_redact_hash <== step_in.tran_hash;
    signal block_hash <== ArrayHasher(blockSize)(block);

    component selector = Mux1();
    selector.c[0] <== PairHasher()(prev_redact_hash, block_hash);
    selector.c[1] <== PairHasher()(prev_redact_hash, 0);
    selector.s <== redact;

    // Update IVC state
    step_out.orig_hash <== PairHasher()(step_in.orig_hash, block_hash);
    step_out.tran_hash <== selector.out;
}