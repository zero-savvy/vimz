use std::collections::HashMap;

use nova_scotia::{
    circom::{circuit::R1CS, reader::load_r1cs},
    create_public_params, create_recursive_circuit, FileLocation, C1, C2, F,
};
use nova_snark::{PublicParams, RecursiveSNARK};
use serde_json::Value;

use crate::{
    config::Config,
    nova_snark_backend::{G1, G2},
};

type FoldingParams = PublicParams<G1, G2, C1<G1>, C2<G2>>;
type FoldingProof = RecursiveSNARK<G1, G2, C1<G1>, C2<G2>>;

/// Prepare the Nova folding scheme with the given config.
pub fn prepare_folding(config: &Config) -> (R1CS<F<G1>>, FoldingParams) {
    let r1cs = load_r1cs::<G1, G2>(&FileLocation::PathBuf(config.circuit_file()));
    let pp: PublicParams<G1, G2, _, _> = create_public_params(r1cs.clone());
    (r1cs, pp)
}

pub fn fold_input(
    config: &Config,
    r1cs: R1CS<F<G1>>,
    ivc_step_inputs: Vec<HashMap<String, Value>>,
    initial_state: Vec<F<G1>>,
    params: &FoldingParams,
) -> FoldingProof {
    create_recursive_circuit(
        FileLocation::PathBuf(config.witness_generator_file()),
        r1cs,
        ivc_step_inputs,
        initial_state,
        params,
    )
    .expect("Failed to fold input")
}

pub fn verify_folded_proof(
    proof: &FoldingProof,
    params: &FoldingParams,
    num_steps: usize,
    initial_state: &[F<G1>],
    secondary_initial_state: &[F<G2>],
) {
    proof
        .verify(params, num_steps, initial_state, secondary_initial_state)
        .expect("Failed to verify folded proof");
}
