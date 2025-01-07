use ark_bn254::{Bn254, Fr, G1Projective as G1};
use ark_grumpkin::Projective as G2;
use rand::{CryptoRng, RngCore};
use sonobe::{
    commitment::{kzg::KZG, pedersen::Pedersen},
    folding::nova::{Nova, PreprocessorParam},
    frontend::FCircuit,
    transcript::poseidon::poseidon_canonical_config,
    FoldingScheme,
};
use sonobe_frontends::circom::CircomFCircuit;
use tracing::info_span;

use crate::config::Config;

/// The folding scheme used.
pub type Folding = Nova<G1, G2, CircomFCircuit<Fr>, KZG<'static, Bn254>, Pedersen<G2>, false>;
pub type FoldingParams = (
    <Folding as FoldingScheme<G1, G2, CircomFCircuit<Fr>>>::ProverParam,
    <Folding as FoldingScheme<G1, G2, CircomFCircuit<Fr>>>::VerifierParam,
);

/// Prepare the Nova folding scheme with the given files, parameters and rng. Initialize it with
/// the given initial state.
#[tracing::instrument(name = "Prepare folding", skip_all)]
pub fn prepare_folding(
    config: &Config,
    initial_state: Vec<Fr>,
    rng: &mut (impl RngCore + CryptoRng),
) -> (Folding, FoldingParams) {
    let f_circuit = create_circuit(config, initial_state.len());

    let nova_params = info_span!("Preprocess Nova").in_scope(|| {
        let nova_preprocess_params =
            PreprocessorParam::new(poseidon_canonical_config::<Fr>(), f_circuit.clone());
        Folding::preprocess(&mut *rng, &nova_preprocess_params).expect("Failed to preprocess Nova")
    });
    let nova = info_span!("Init Nova").in_scope(|| {
        Folding::init(&nova_params, f_circuit, initial_state).expect("Failed to init Nova")
    });

    (nova, nova_params)
}

/// Create a new `CircomFCircuit` for the given configuration.
#[tracing::instrument(name = "Create circuit", skip_all)]
fn create_circuit(config: &Config, ivc_state_width: usize) -> CircomFCircuit<Fr> {
    let f_circuit_params = (
        config.circuit_file().into(),
        config.witness_generator_file().into(),
        ivc_state_width,
        config.function.step_input_width(),
    );
    CircomFCircuit::<Fr>::new(f_circuit_params).expect("Failed to create circuit")
}

/// Fold all the `ivc_steps_inputs` into `folding`.
#[tracing::instrument(name = "Fold input", skip_all, fields(steps = ivc_step_inputs.len()))]
pub fn fold_input(folding: &mut Folding, ivc_step_inputs: Vec<Vec<Fr>>, rng: &mut impl RngCore) {
    for (i, ivc_step_input) in ivc_step_inputs.into_iter().enumerate() {
        info_span!("Fold step", completed = i).in_scope(|| {
            folding
                .prove_step(&mut *rng, ivc_step_input, None)
                .expect("Failed to prove step")
        });
    }
}

#[tracing::instrument(name = "Verify folded proof", skip_all)]
pub fn verify_folding(folding: &Folding, folding_params: &FoldingParams) {
    Folding::verify(folding_params.1.clone(), folding.ivc_proof())
        .expect("Failed to verify folded proof");
}
