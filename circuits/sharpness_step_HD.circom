pragma circom 2.0.0;

include "utils/sharpness_step.circom";


component main { public [step_in] } = Sharpen(128, 3);
