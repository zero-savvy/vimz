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
        CRHGadget::<F>::evaluate(&crh_params, &[state.source_hash, block_hash.clone()])?;

    // TODO: add constant for hash of the empty block (to be consistent with off-circuit image hash)
    let redacted_hash = CRHGadget::<F>::evaluate(&crh_params, &[state.target_hash.clone()])?;
    let nonredacted_hash = CRHGadget::<F>::evaluate(&crh_params, &[state.target_hash, block_hash])?;
    let target_hash = redaction_indicator.select(&redacted_hash, &nonredacted_hash)?;

    Ok(vec![source_hash, target_hash])
}

circuit_from_step_function!(Redact, generate_step_constraints);
