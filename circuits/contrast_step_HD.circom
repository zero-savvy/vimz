pragma circom 2.0.0;

include "utils/contrast_step.circom";

component main { public [step_in] } = ContrastHash(128);



