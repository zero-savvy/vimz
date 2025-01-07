use rand::{prelude::StdRng, SeedableRng};
use sonobe::Decider as _;
use tracing::info_span;

use crate::{
    config::Config,
    sonobe_backend::{
        decider::{verify_final_proof, Decider},
        folding::{fold_input, prepare_folding, verify_folding},
        input::prepare_input,
        solidity::verify_on_chain,
    },
};

mod decider;
mod folding;
mod input;
mod solidity;

pub fn run(config: &Config) {
    let mut rng = StdRng::from_seed([41; 32]);

    // ========================== Prepare input and folding ========================================

    let (ivc_step_inputs, initial_state) = prepare_input(config);
    let num_steps = ivc_step_inputs.len() as u32;
    let (mut folding, folding_params) = prepare_folding(config, initial_state.clone(), &mut rng);

    // ========================== Fold the input and verify the folding proof ======================

    fold_input(&mut folding, ivc_step_inputs, &mut rng);
    verify_folding(&folding, &folding_params, initial_state, num_steps);

    // ========================== Prepare decider and compress the proof ===========================

    let (decider_pp, decider_vp) = info_span!("Prepare decider").in_scope(|| {
        Decider::preprocess(&mut rng, folding_params, folding.clone())
            .expect("Failed to preprocess decider")
    });
    let proof = info_span!("Generate decider proof").in_scope(|| {
        Decider::prove(rng, decider_pp, folding.clone()).expect("Failed to generate proof")
    });

    // ========================== Verify the final proof ===========================================

    verify_final_proof(&proof, &folding, decider_vp.clone());
    verify_on_chain(&folding.F.clone(), decider_vp, folding, proof);
}
