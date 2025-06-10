use std::fs;

use clap::Parser;
use rand::{SeedableRng, prelude::StdRng};
use sonobe::Decider as _;
use sonobe_solidity::{NovaCycleFoldVerifierKey, get_decider_template_for_cyclefold_decider};
use vimz::{
    config::{Backend, Config},
    logging::init_logging,
    sonobe_backend::{
        circuits::{SonobeCircuit, circom::*},
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
        Transformation::Blur => run::<BlurCircomCircuit>(&config),
        Transformation::Brightness => run::<BrightnessCircomCircuit>(&config),
        Transformation::Contrast => run::<ContrastCircomCircuit>(&config),
        Transformation::Crop => run::<CropCircomCircuit>(&config),
        Transformation::Grayscale => run::<GrayscaleCircomCircuit>(&config),
        Transformation::Hash => run::<HashCircomCircuit>(&config),
        Transformation::Redact => run::<RedactCircomCircuit>(&config),
        Transformation::Resize => run::<ResizeCircomCircuit>(&config),
        Transformation::Sharpness => run::<SharpnessCircomCircuit>(&config),
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
    let initial_state_len = initial_state.len();
    let (_, folding_params) = prepare_folding::<Circuit>(config, initial_state, &mut rng);

    Decider::<Circuit>::preprocess(&mut rng, (folding_params, initial_state_len))
        .expect("Failed to preprocess decider")
        .1
}
