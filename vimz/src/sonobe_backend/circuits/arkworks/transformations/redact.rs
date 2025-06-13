use ark_crypto_primitives::{
    crh::{
        CRHSchemeGadget,
        poseidon::constraints::{CRHGadget, CRHParametersVar},
    },
    sponge::Absorb,
};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    R1CSVar, alloc::AllocVar, boolean::Boolean, convert::ToConstraintFieldGadget, eq::EqGadget,
    fields::fp::FpVar,
};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

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

    // hack to safely cast FpVar<F> to Boolean<F>
    let redaction_indicator_fp = external_inputs.pop().unwrap();
    let redaction_indicator = Boolean::new_witness(cs.clone(), || {
        Ok(redaction_indicator_fp.value()? == F::one())
    })?;
    redaction_indicator_fp.enforce_equal(&redaction_indicator.to_constraint_field()?[0])?;

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
