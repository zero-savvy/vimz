use std::fs;

use nova_scotia::S;
use nova_snark::CompressedSNARK;
use tracing::info_span;

use crate::{
    config::Config,
    nova_snark_backend::{
        folding::{fold_input, prepare_folding, verify_folded_proof},
        input::{prepare_input, PreparedInputs},
    },
};

mod folding;
mod input;

type G1 = nova_snark::provider::bn256_grumpkin::bn256::Point;
type G2 = nova_snark::provider::bn256_grumpkin::grumpkin::Point;

pub fn run(config: &Config) {
    // ========================== Prepare input and folding ========================================

    let PreparedInputs {
        ivc_step_inputs,
        initial_state,
        secondary_initial_state,
    } = prepare_input(config);
    let num_steps = ivc_step_inputs.len();
    let (r1cs, folding_params) = prepare_folding(config);

    // ========================== Fold the input and verify the folding proof ======================

    let folding_proof = fold_input(
        config,
        r1cs,
        ivc_step_inputs,
        initial_state.clone(),
        &folding_params,
    );
    verify_folded_proof(
        &folding_proof,
        &folding_params,
        num_steps,
        &initial_state,
        &secondary_initial_state,
    );

    // ========================== Prepare compression and compress the proof =======================

    let (pk, vk) = info_span!("Prepare compression").in_scope(|| {
        CompressedSNARK::<_, _, _, _, S<G1>, S<G2>>::setup(&folding_params)
            .expect("Failed to setup compression")
    });
    let compressed_proof = info_span!("Compress proof").in_scope(|| {
        CompressedSNARK::<_, _, _, _, S<G1>, S<G2>>::prove(&folding_params, &pk, &folding_proof)
            .expect("Failed to compress proof")
    });

    // ========================== Verify the final proof ===========================================

    info_span!("Verify compressed proof").in_scope(|| {
        compressed_proof
            .verify(&vk, num_steps, initial_state, secondary_initial_state)
            .expect("Failed to verify proof");
    });

    // ========================== Save final proof =================================================

    if let Some(output_file) = config.output_file() {
        info_span!("Save proof").in_scope(|| {
            fs::write(
                output_file,
                serde_json::to_string_pretty(&compressed_proof).unwrap(),
            )
            .expect("Failed to write proof to file");
        });
    }
}
