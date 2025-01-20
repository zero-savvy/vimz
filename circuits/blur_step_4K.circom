pragma circom 2.0.0;

include "utils/blur_step.circom";

component main { public [step_in] } = Blur(384, 3);
