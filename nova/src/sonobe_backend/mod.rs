use ark_bn254::Fr;
use sonobe::{Decider as _, FoldingScheme};

use crate::{
    config::Config,
    input::VIMzInput,
    sonobe_backend::{
        folding::{prepare_folding, verify_final_proof, Decider},
        input::{prepare_input, step_input_width},
        solidity::verify_on_chain,
    },
    time::measure,
};

mod folding;
mod input;
mod solidity;

pub fn run(config: &Config) {
    let mut rng = rand::rngs::OsRng;

    let private_inputs = measure("Prepare private inputs", || {
        VIMzInput::<Fr>::from_file(&config.input)
    });

    let initial_state = config.function.ivc_initial_state(&private_inputs.extra);
    let (mut folding, decider_pp, decider_vp) = prepare_folding(
        &config.circuit,
        &config.witness_generator,
        initial_state.len(),
        step_input_width(config.function),
        initial_state,
        &mut rng,
    );

    let prepared_input = prepare_input(config.function, private_inputs);
    assert_eq!(prepared_input.len(), config.resolution.iteration_count());
    for (i, external_inputs_at_step) in prepared_input[..5].iter().enumerate() {
        measure(&format!("Nova::prove_step {i}"), || {
            folding
                .prove_step(rng, external_inputs_at_step.clone(), None)
                .expect("Failed to prove step")
        });
    }

    let proof = measure("Generated decider proof", || {
        Decider::prove(rng, decider_pp, folding.clone()).expect("Failed to generate proof")
    });

    assert!(verify_final_proof(&proof, &folding, decider_vp.clone()));

    verify_on_chain(&folding.F.clone(), decider_vp, folding, proof);
}
