use nova_scotia::{F, S};
use nova_snark::CompressedSNARK;

use crate::{
    config::Config,
    nova_snark_backend::{
        folding::{fold_input, prepare_folding, verify_folded_proof},
        input::prepare_input,
    },
    time::measure,
};

mod folding;
mod input;

type G1 = nova_snark::provider::bn256_grumpkin::bn256::Point;
type G2 = nova_snark::provider::bn256_grumpkin::grumpkin::Point;

type Fr = F<G1>;

pub fn run(config: &Config) {
    // ========================== Prepare input and folding ========================================

    let (ivc_step_inputs, initial_state, secondary_initial_state) =
        measure("Prepare input", || prepare_input(config));
    let num_steps = ivc_step_inputs.len();
    let (r1cs, folding_params) = prepare_folding(config);

    // ========================== Fold the input and verify the folding proof ======================

    let folding_proof = measure("Nova folding", || {
        fold_input(
            config,
            r1cs,
            ivc_step_inputs,
            initial_state.clone(),
            &folding_params,
        )
    });
    verify_folded_proof(
        &folding_proof,
        &folding_params,
        num_steps,
        &initial_state,
        &secondary_initial_state,
    );

    // ========================== Prepare compression and compress the proof =======================

    let (pk, vk) = CompressedSNARK::<_, _, _, _, S<G1>, S<G2>>::setup(&folding_params).unwrap();
    let compressed_proof =
        CompressedSNARK::<_, _, _, _, S<G1>, S<G2>>::prove(&folding_params, &pk, &folding_proof)
            .expect("Failed to compress proof");

    // ========================== Verify the final proof ===========================================

    compressed_proof
        .verify(&vk, num_steps, initial_state, secondary_initial_state)
        .expect("Failed to verify proof");
}
