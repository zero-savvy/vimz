use std::fs;

use ark_bn254::Fr;
use rand::{prelude::StdRng, SeedableRng};
use sonobe::Decider as _;
use tracing::info_span;

use crate::{
    config::{Config, Frontend},
    sonobe_backend::{
        circuits::{arkworks::*, circom::*, SonobeCircuit},
        decider::{verify_final_proof, Decider},
        folding::{fold_input, prepare_folding, verify_folding},
        input::prepare_input,
        solidity::prepare_contract_calldata,
    },
    transformation::Transformation,
};

pub mod circuits;
pub mod decider;
pub mod folding;
pub mod input;
pub mod solidity;

pub fn run(config: &Config) {
    match config.frontend {
        Frontend::Circom => match config.function {
            Transformation::Blur => _run::<BlurCircomCircuit>(config),
            Transformation::Brightness => _run::<BrightnessCircomCircuit>(config),
            Transformation::Contrast => _run::<ContrastCircomCircuit>(config),
            Transformation::Crop => _run::<CropCircomCircuit>(config),
            Transformation::Grayscale => _run::<GrayscaleCircomCircuit>(config),
            Transformation::Hash => _run::<HashCircomCircuit>(config),
            Transformation::Redact => _run::<RedactCircomCircuit>(config),
            Transformation::Resize => _run::<ResizeCircomCircuit>(config),
            Transformation::Sharpness => _run::<SharpnessCircomCircuit>(config),
        },
        Frontend::Arkworks => match config.function {
            Transformation::Hash => _run::<HashArkworksCircuit<Fr>>(config),
            Transformation::Brightness => _run::<BrightnessArkworksCircuit<Fr>>(config),
            Transformation::Contrast => _run::<ContrastArkworksCircuit<Fr>>(config),
            Transformation::Grayscale => _run::<GrayscaleArkworksCircuit<Fr>>(config),
            Transformation::Redact => _run::<RedactArkworksCircuit<Fr>>(config),
            _ => unimplemented!("Not supported for Arkworks frontend yet"),
        },
    }
}

fn _run<Circuit: SonobeCircuit>(config: &Config) {
    let mut rng = StdRng::from_seed([41; 32]);

    // ========================== Prepare input and folding ========================================

    let (ivc_step_inputs, initial_state) = prepare_input(config);
    let (mut folding, folding_params) =
        prepare_folding::<Circuit>(config, initial_state.clone(), &mut rng);

    // ========================== Fold the input and verify the folding proof ======================

    fold_input(&mut folding, ivc_step_inputs, &mut rng);
    verify_folding(&folding, &folding_params);

    // ========================== Prepare decider and compress the proof ===========================

    let (decider_pp, decider_vp) = info_span!("Prepare decider").in_scope(|| {
        Decider::<Circuit>::preprocess(&mut rng, (folding_params, initial_state.len()))
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

        fs::write(output_file, prepare_contract_calldata(&folding, &proof))
            .expect("Failed to write calldata to file");
    }
}
