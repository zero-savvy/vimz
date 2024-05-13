pragma circom 2.0.0;

include "node_modules/circomlib/circuits/multiplexer.circom";
include "node_modules/circomlib/circuits/mux1.circom";
include "node_modules/circomlib/circuits/comparators.circom";
include "utils/pixels.circom";
include "utils/row_hasher.circom";


template Support(Height){
    // public inputs
    signal input step_in[3];
    
    // private inputs
    signal input row_hash;
    
    //outputs
    signal output step_out[3];
    
    // Decode input Signals
    var crop_finish_y = step_in[0];
    var index = step_in[1];
    var prev_hash = step_in[2];

    component hasher = Hasher(2);
    hasher.values[0] <== prev_hash;
    hasher.values[1] <== row_hash;

    component gt = GreaterThan(12);
    gt.in[0] <== index;
    gt.in[1] <== crop_finish_y;

    component selector = Mux1();
    selector.c[0] <== prev_hash;
    selector.c[1] <== hasher.hash;
    selector.s <== gt.out;

    step_out[0] <== crop_finish_y;
    step_out[1] <== index + 1;
    step_out[2] <== selector.out;

}

component main { public [step_in] } = Support(720);