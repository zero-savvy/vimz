pragma circom 2.0.0;

include "utils/crop_step.circom";

component main { public [step_in] } = CropHash(384, 64, 480);
