use std::{env::current_dir, path::Path};

use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as G1};
use ark_groth16::Groth16;
use ark_grumpkin::{constraints::GVar as GVar2, Projective as G2};
use rand::{CryptoRng, RngCore};
use sonobe::{
    commitment::{kzg::KZG, pedersen::Pedersen},
    folding::nova::{decider_eth::Decider as DeciderEth, Nova, PreprocessorParam},
    frontend::{circom::CircomFCircuit, FCircuit},
    transcript::poseidon::poseidon_canonical_config,
    Decider as DeciderTrait, FoldingScheme,
};

use crate::time::measure;

pub type Folding =
    Nova<G1, GVar, G2, GVar2, CircomFCircuit<Fr>, KZG<'static, Bn254>, Pedersen<G2>, false>;
pub type Decider = DeciderEth<
    G1,
    GVar,
    G2,
    GVar2,
    CircomFCircuit<Fr>,
    KZG<'static, Bn254>,
    Pedersen<G2>,
    Groth16<Bn254>,
    Folding,
>;
type DeciderProverParam =
    <Decider as DeciderTrait<G1, G2, CircomFCircuit<Fr>, Folding>>::ProverParam;
type DeciderVerifierParam =
    <Decider as DeciderTrait<G1, G2, CircomFCircuit<Fr>, Folding>>::VerifierParam;
type DeciderProof = <Decider as DeciderTrait<G1, G2, CircomFCircuit<Fr>, Folding>>::Proof;

/// Prepare the Nova folding scheme with the given files, parameters and rng. Initialize it with
/// the given initial state.
///
/// Assumes that the file paths are relative to the current directory.
pub fn prepare_folding(
    circuit_file: &Path,
    witness_generator_file: &Path,
    ivc_state_width: usize,
    step_input_width: usize,
    start_ivc_state: Vec<Fr>,
    rng: &mut (impl RngCore + CryptoRng),
) -> (Folding, DeciderProverParam, DeciderVerifierParam) {
    let f_circuit = measure("Prepare circuit", || {
        create_circuit(
            circuit_file,
            witness_generator_file,
            ivc_state_width,
            step_input_width,
        )
    });

    let nova_params = measure("Nova preprocess", || {
        let nova_preprocess_params =
            PreprocessorParam::new(poseidon_canonical_config::<Fr>(), f_circuit.clone());
        Folding::preprocess(&mut *rng, &nova_preprocess_params).expect("Failed to preprocess Nova")
    });
    let nova = measure("Nova init", || {
        Folding::init(&nova_params, f_circuit.clone(), start_ivc_state)
            .expect("Failed to init Nova")
    });
    let (decider_pp, decider_vp) = measure("Decider preprocess", || {
        Decider::preprocess(&mut *rng, &nova_params, nova.clone()).unwrap()
    });

    (nova, decider_pp, decider_vp)
}

/// Create a new `CircomFCircuit` from the given files and parameters.
///
/// Assumes that the file paths are relative to the current directory.
fn create_circuit(
    circuit_file: &Path,
    witness_generator_file: &Path,
    ivc_state_width: usize,
    step_input_width: usize,
) -> CircomFCircuit<Fr> {
    let root = current_dir().expect("Failed to get current directory");
    let circuit_file = root.join(circuit_file);
    let witness_generator_file = root.join(witness_generator_file);

    let f_circuit_params = (
        circuit_file,
        witness_generator_file,
        ivc_state_width,
        step_input_width,
    );
    CircomFCircuit::<Fr>::new(f_circuit_params).expect("Failed to create circuit")
}

/// Verify the final proof generated by the Nova folding scheme and the decider wrapper.
///
/// Returns `true` if the proof is valid, `false` otherwise.
pub fn verify_final_proof(
    proof: &DeciderProof,
    folding: &Folding,
    decider_vp: DeciderVerifierParam,
) -> bool {
    Decider::verify(
        decider_vp,
        folding.i,
        folding.z_0.clone(),
        folding.z_i.clone(),
        &folding.U_i,
        &folding.u_i,
        proof,
    )
    .expect("Failed to verify proof")
}
