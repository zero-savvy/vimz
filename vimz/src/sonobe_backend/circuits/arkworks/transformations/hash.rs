use ark_crypto_primitives::{
    crh::{
        CRHSchemeGadget,
        poseidon::constraints::{CRHGadget, CRHParametersVar},
    },
    sponge::Absorb,
};
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

use crate::{circuit_from_step_function, transformation::Transformation};

fn generate_step_constraints<F: PrimeField + Absorb>(
    _cs: ConstraintSystemRef<F>,
    z_i: Vec<FpVar<F>>,
    external_inputs: Vec<FpVar<F>>,
    crh_params: CRHParametersVar<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let old_hash = z_i[0].clone();
    let hash_input = [&[old_hash], external_inputs.as_slice()].concat();
    let h = CRHGadget::<F>::evaluate(&crh_params, &hash_input)?;
    Ok(vec![h])
}

circuit_from_step_function!(Hash, generate_step_constraints);
