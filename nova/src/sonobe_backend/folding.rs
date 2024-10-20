use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as G1};
use ark_grumpkin::{constraints::GVar as GVar2, Projective as G2};
use rand::{CryptoRng, RngCore};
use sonobe::{
    commitment::{kzg::KZG, pedersen::Pedersen},
    folding::nova::{Nova, PreprocessorParam},
    frontend::{circom::CircomFCircuit, FCircuit},
    transcript::poseidon::poseidon_canonical_config,
    FoldingScheme,
};

use crate::{config::Config, time::measure};

/// The folding scheme used.
pub type Folding =
    Nova<G1, GVar, G2, GVar2, CircomFCircuit<Fr>, KZG<'static, Bn254>, Pedersen<G2>, false>;
pub type FoldingParams = (
    <Folding as FoldingScheme<G1, G2, CircomFCircuit<Fr>>>::ProverParam,
    <Folding as FoldingScheme<G1, G2, CircomFCircuit<Fr>>>::VerifierParam,
);

/// Prepare the Nova folding scheme with the given files, parameters and rng. Initialize it with
/// the given initial state.
pub fn prepare_folding(
    config: &Config,
    initial_state: Vec<Fr>,
    rng: &mut (impl RngCore + CryptoRng),
) -> (Folding, FoldingParams) {
    let f_circuit = measure("Prepare circuit", || {
        create_circuit(config, initial_state.len())
    });

    let nova_params = measure("Nova preprocess", || {
        let nova_preprocess_params =
            PreprocessorParam::new(poseidon_canonical_config::<Fr>(), f_circuit.clone());
        Folding::preprocess(&mut *rng, &nova_preprocess_params).expect("Failed to preprocess Nova")
    });
    let nova = measure("Nova init", || {
        Folding::init(&nova_params, f_circuit, initial_state).expect("Failed to init Nova")
    });

    (nova, nova_params)
}

/// Create a new `CircomFCircuit` for the given configuration.
fn create_circuit(config: &Config, ivc_state_width: usize) -> CircomFCircuit<Fr> {
    let f_circuit_params = (
        config.circuit_file(),
        config.witness_generator_file(),
        ivc_state_width,
        config.function.step_input_width(),
    );
    CircomFCircuit::<Fr>::new(f_circuit_params).expect("Failed to create circuit")
}

/// Fold all the `ivc_steps_inputs` into `folding`.
pub fn fold_input(folding: &mut Folding, ivc_step_inputs: Vec<Vec<Fr>>, rng: &mut impl RngCore) {
    for (i, ivc_step_input) in ivc_step_inputs.into_iter().enumerate().take(5) {
        measure(&format!("Nova::prove_step {i}"), || {
            folding
                .prove_step(&mut *rng, ivc_step_input, None)
                .expect("Failed to prove step")
        });
    }
}

pub fn verify_folding(
    folding: &Folding,
    folding_params: &FoldingParams,
    initial_state: Vec<Fr>,
    num_steps: u32,
) {
    let (running_instance, incoming_instance, cyclefold_instance) = folding.instances();
    Folding::verify(
        folding_params.1.clone(),
        initial_state,
        folding.state(),
        Fr::from(num_steps),
        running_instance,
        incoming_instance,
        cyclefold_instance,
    )
    .expect("Failed to verify folded proof");
}
