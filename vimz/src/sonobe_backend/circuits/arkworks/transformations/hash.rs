use ark_crypto_primitives::{
    crh::{
        CRHSchemeGadget, TwoToOneCRHSchemeGadget,
        poseidon::constraints::{CRHGadget, CRHParametersVar, TwoToOneCRHGadget},
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
    let row_hash = CRHGadget::<F>::evaluate(&crh_params, &external_inputs)?;
    let updated_hash = TwoToOneCRHGadget::<F>::evaluate(&crh_params, &z_i[0], &row_hash)?;
    Ok(vec![updated_hash])
}

circuit_from_step_function!(Hash, generate_step_constraints);
