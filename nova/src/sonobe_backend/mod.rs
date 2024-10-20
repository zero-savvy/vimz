use decider::prepare_decider;
use sonobe::{Decider as _, FoldingScheme};

use crate::{
    config::Config,
    sonobe_backend::{
        decider::{verify_final_proof, Decider},
        folding::prepare_folding,
        input::prepare_input,
        solidity::verify_on_chain,
    },
    time::measure,
};

mod decider;
mod folding;
mod input;
mod solidity;

pub fn run(config: &Config) {
    let mut rng = rand::rngs::OsRng;

    // ============================== Prepare input and folding ====================================

    let (ivc_step_inputs, initial_state) = measure("Prepare input", || prepare_input(config));
    let (mut folding, folding_params) = prepare_folding(config, initial_state, &mut rng);

    // ============================== Fold the input ===============================================

    for (i, ivc_step_input) in ivc_step_inputs.into_iter().enumerate().take(5) {
        measure(&format!("Nova::prove_step {i}"), || {
            folding
                .prove_step(rng, ivc_step_input, None)
                .expect("Failed to prove step")
        });
    }

    // ============================== Prepare decider and compress the proof =======================

    let (decider_pp, decider_vp) = prepare_decider(folding.clone(), folding_params, &mut rng);
    let proof = measure("Generated decider proof", || {
        Decider::prove(rng, decider_pp, folding.clone()).expect("Failed to generate proof")
    });

    // ============================== Verify the final proof =======================================

    verify_final_proof(&proof, &folding, decider_vp.clone());
    verify_on_chain(&folding.F.clone(), decider_vp, folding, proof);
}
