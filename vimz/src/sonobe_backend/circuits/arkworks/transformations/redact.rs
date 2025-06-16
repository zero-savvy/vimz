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
use arkworks_small_values_ops::cast_to_boolean;

use crate::{
    circuit_from_step_function,
    sonobe_backend::circuits::arkworks::ivc_state::{IVCState, IVCStateT},
    transformation::Transformation,
};

fn generate_step_constraints<F: PrimeField + Absorb>(
    cs: ConstraintSystemRef<F>,
    z_i: Vec<FpVar<F>>,
    mut external_inputs: Vec<FpVar<F>>,
    crh_params: CRHParametersVar<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let state = IVCState::new(z_i);

    let redaction_indicator = cast_to_boolean(cs.clone(), &external_inputs.pop().unwrap())?;

    let block_hash = CRHGadget::<F>::evaluate(&crh_params, &external_inputs)?;

    let source_hash =
        TwoToOneCRHGadget::<F>::evaluate(&crh_params, &state.source_hash, &block_hash)?;

    let mut zeros = vec![];
    for _ in 0..external_inputs.len() {
        zeros.push(FpVar::Constant(F::zero()));
    }
    let redacted_hash = CRHGadget::<F>::evaluate(&crh_params, zeros.as_slice())?;

    let target_hash = redaction_indicator.select(
        &TwoToOneCRHGadget::<F>::evaluate(&crh_params, &state.target_hash, &redacted_hash)?,
        &TwoToOneCRHGadget::<F>::evaluate(&crh_params, &state.target_hash, &block_hash)?,
    )?;

    Ok(vec![source_hash, target_hash])
}

circuit_from_step_function!(Redact, generate_step_constraints);
