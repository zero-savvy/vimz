use ark_bn254::Fr;
use clap::Parser;
use folding::prepare_folding;
use sonobe::{Decider as _, FoldingScheme};

use crate::{
    config::Config,
    folding::{verify_final_proof, Decider},
    input::ZKronoInput,
    time::measure,
};

mod config;
mod folding;
mod input;
mod time;
mod transformation;

fn get_private_inputs(config: &Config) -> Vec<Vec<Fr>> {
    let private_inputs = measure("Prepare private inputs", || {
        ZKronoInput::from_file(&config.input).into_circom_input()
    });
    assert_eq!(
        private_inputs.len(),
        config.resolution.iteration_count(),
        "Invalid input length - does not match resolution iteration count"
    );
    private_inputs
}

fn fold_fold_fold(config: &Config) {
    let mut rng = rand::rngs::OsRng;

    let (mut folding, decider_pp, decider_vp) = prepare_folding(
        &config.circuit,
        &config.witness_generator,
        2,
        8,
        vec![0.into(); 2],
        &mut rng,
    );

    let private_inputs = get_private_inputs(&config);
    for (i, external_inputs_at_step) in private_inputs[..5].iter().enumerate() {
        measure(&format!("Nova::prove_step {i}"), || {
            folding
                .prove_step(rng, external_inputs_at_step.clone(), None)
                .expect("Failed to prove step")
        });
    }

    let proof = measure("Generated decider proof", || {
        Decider::prove(rng, decider_pp, folding.clone()).expect("Failed to generate proof")
    });

    assert!(verify_final_proof(&proof, &folding, decider_vp));
}

fn main() {
    let config = Config::parse();
    config.display();
    fold_fold_fold(&config);
}
