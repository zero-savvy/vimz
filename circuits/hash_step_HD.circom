pragma circom 2.0.0;

include "utils/hash_step.circom";

component main { public [step_in] } = CropHash(128);
