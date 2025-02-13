use std::fs;

use rand::{prelude::StdRng, SeedableRng};
use sonobe::Decider as _;
use tracing::info_span;

use crate::{
    config::Config,
    sonobe_backend::{
        decider::{verify_final_proof, Decider},
        folding::{fold_input, prepare_folding, verify_folding},
        input::prepare_input,
        solidity::prepare_contract_calldata,
    },
};

pub mod decider;
pub mod folding;
pub mod input;
pub mod solidity;

pub fn run(config: &Config) {
    let mut rng = StdRng::from_seed([41; 32]);

    // ========================== Prepare input and folding ========================================

    let (ivc_step_inputs, initial_state) = prepare_input(config);
    let (mut folding, folding_params) = prepare_folding(config, initial_state.clone(), &mut rng);

    // ========================== Fold the input and verify the folding proof ======================

    fold_input(&mut folding, ivc_step_inputs, &mut rng);
    verify_folding(&folding, &folding_params);

    // ========================== Prepare decider and compress the proof ===========================

    let (decider_pp, decider_vp) = info_span!("Prepare decider").in_scope(|| {
        Decider::preprocess(&mut rng, folding_params, folding.clone())
            .expect("Failed to preprocess decider")
    });
    let proof = info_span!("Generate decider proof").in_scope(|| {
        Decider::prove(rng, decider_pp, folding.clone()).expect("Failed to generate proof")
    });

    // ========================== Verify the final proof locally ===================================

    verify_final_proof(&proof, &folding, decider_vp.clone());

    // ========================== Prepare calldata for on-chain verification =======================

    if let Some(output_file) = config.output_file() {
        // Ensure the parent directory exists
        if let Some(parent_dir) = output_file.parent() {
            fs::create_dir_all(parent_dir).expect("Failed to create output directory");
        }

        fs::write(output_file, prepare_contract_calldata(&folding, proof))
            .expect("Failed to write calldata to file");
    }
}
