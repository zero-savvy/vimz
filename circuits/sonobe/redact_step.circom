pragma circom 2.2.0;

include "../src/redact_step.circom";
include "../src/utils/input_transformation.circom";
include "../src/utils/state.circom";

// Sonobe wrapper over `RedactHash` circuit.
template SonobeRedact(blockSize){
    // ---- Running IVC state ----
    input  IVCStateWithInfo ivc_input;
    output IVCStateWithInfo ivc_output;
    // ---- Step inputs ----
    signal input  external_inputs[blockSize];
    // ---- Step computation ----
    ivc_output <== RedactHash(blockSize)(ivc_input, external_inputs);
}

component main { public [ivc_input] } = SonobeRedact(32*32);
