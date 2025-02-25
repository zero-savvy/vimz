pragma circom 2.2.0;

include "../src/redact_step.circom";
include "../src/utils/input_transformation.circom";
include "../src/utils/state.circom";

// Sonobe wrapper over `RedactHash` circuit.
template SonobeRedact(blockSize){
    // ---- Running IVC state ----
    input  IVCState ivc_input;
    output IVCState ivc_output;
    // ---- Step inputs ----
    signal input external_inputs[blockSize + 1];
    // ---- Input transformation ----
    signal block[blockSize], redact;
    (block, redact) <== ArrayWithScalarInput(blockSize)(external_inputs);
    // ---- Step computation ----
    ivc_output <== RedactHash(blockSize)(ivc_input, block, redact);
}

component main { public [ivc_input] } = SonobeRedact(160); // block is 40x40, with 10-pixel compression
