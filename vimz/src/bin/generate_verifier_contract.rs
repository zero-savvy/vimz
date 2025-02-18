use std::fs;

use clap::Parser;
use rand::{prelude::StdRng, SeedableRng};
use sonobe::Decider as _;
use sonobe_solidity::{get_decider_template_for_cyclefold_decider, NovaCycleFoldVerifierKey};
use vimz::{
    config::{Backend, Config},
    logging::init_logging,
    sonobe_backend::{
        circuit::{
            BlurCircuit, BrightnessCircuit, ContrastCircuit, CropCircuit, GrayscaleCircuit,
            HashCircuit, ResizeCircuit, SharpnessCircuit, SonobeCircuit,
        },
        decider::{Decider, DeciderVerifierParam},
        folding::prepare_folding,
        input::prepare_input,
    },
    transformation::Transformation,
};

fn main() {
    init_logging();

    let config = Config::parse();
    if matches!(config.backend, Backend::NovaSnark) {
        panic!("NovaSnark does not support verifier contract generation");
    }

    match config.function {
        Transformation::Blur => run::<BlurCircuit>(&config),
        Transformation::Brightness => run::<BrightnessCircuit>(&config),
        Transformation::Contrast => run::<ContrastCircuit>(&config),
        Transformation::Crop => run::<CropCircuit>(&config),
        Transformation::Grayscale => run::<GrayscaleCircuit>(&config),
        Transformation::Hash => run::<HashCircuit>(&config),
        Transformation::Resize => run::<ResizeCircuit>(&config),
        Transformation::Sharpness => run::<SharpnessCircuit>(&config),
    }
}

fn run<Circuit: SonobeCircuit>(config: &Config) {
    let decider_vp = prepare_decider_verification_parameters::<Circuit>(config);

    let nova_cyclefold_vk =
        NovaCycleFoldVerifierKey::from((decider_vp, config.function.ivc_state_len()));
    let code = get_decider_template_for_cyclefold_decider(nova_cyclefold_vk);

    let output_file = config
        .output_file()
        .expect("Output file is not specified")
        .join(format!("{:?}Verifier.sol", config.function));
    fs::write(output_file, code).expect("Failed to write the verifier contract");
}

fn prepare_decider_verification_parameters<Circuit: SonobeCircuit>(
    config: &Config,
) -> DeciderVerifierParam<Circuit> {
    // TODO: USE THE SAME RNG EVERYWHERE
    let mut rng = StdRng::from_seed([41; 32]);

    let (_, initial_state) = prepare_input(config);
    let (folding, folding_params) = prepare_folding::<Circuit>(config, initial_state, &mut rng);

    Decider::preprocess(&mut rng, folding_params, folding)
        .expect("Failed to preprocess decider")
        .1
}
