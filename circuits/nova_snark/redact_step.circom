pragma circom 2.2.0;

include "../src/redact_step.circom";
include "../src/utils/state.circom";

// NovaSnark wrapper over `RedactHash` circuit.
template NovaRedact(blockSize){
    // ---- Running IVC state ----
    input  IVCStateWithInfo step_in;
    output IVCStateWithInfo step_out;
    // ---- Step inputs ----
    signal input row_orig[blockSize];
    signal input redact;
    // ---- Step computation ----
    step_out <== RedactHash(blockSize)(step_in, row_orig, redact);
}

component main { public [step_in] } = NovaRedact(32*32);
