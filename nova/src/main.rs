use backend::Backend;
use clap::Parser;
use folding::prepare_folding;
use nova_snark::nova_snark_backend;
use sonobe::{Decider as _, FoldingScheme};

use crate::{
    config::Config,
    folding::{verify_final_proof, Decider},
    input::ZKronoInput,
    solidity::verify_on_chain,
    time::measure,
};

mod backend;
mod config;
mod folding;
mod input;
mod nova_snark;
mod solidity;
mod time;
mod transformation;

fn sonobe_backend(config: &Config) {
    let mut rng = rand::rngs::OsRng;

    let private_inputs = measure("Prepare private inputs", || {
        ZKronoInput::from_file(&config.input)
    });

    let initial_state = config.function.ivc_initial_state(&private_inputs);
    let (mut folding, decider_pp, decider_vp) = prepare_folding(
        &config.circuit,
        &config.witness_generator,
        initial_state.len(),
        config.function.step_input_width(),
        initial_state,
        &mut rng,
    );

    let prepared_input = config.function.prepare_input(private_inputs);
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

fn fold_fold_fold(config: &Config) {
    match config.backend {
        Backend::NovaSnark => {
            // Call function A here
            nova_snark_backend(config);
        }
        Backend::Sonobe => {
            // Call function B here
            sonobe_backend(config);
        }
    }
}

fn main() {
    let config = Config::parse();
    config.display();
    fold_fold_fold(&config);
}
