pragma circom 2.2.0;

include "../src/redact_step.circom";
include "../src/utils/state.circom";

// NovaSnark wrapper over `RedactHash` circuit.
template NovaRedact(blockSize){
    // ---- Running IVC state ----
    input  IVCState step_in;
    output IVCState step_out;
    // ---- Step inputs ----
    signal input block[blockSize];
    signal input redact;
    // ---- Step computation ----
    step_out <== RedactHash(blockSize)(step_in, block, redact);
}

component main { public [step_in] } = NovaRedact(128);
