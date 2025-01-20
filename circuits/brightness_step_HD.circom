pragma circom 2.0.0;

include "utils/brightness_step.circom";

component main { public [step_in] } = BrightnessHash(128);



