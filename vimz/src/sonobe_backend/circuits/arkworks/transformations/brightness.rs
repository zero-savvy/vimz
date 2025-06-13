use std::ops::Mul;

use ark_crypto_primitives::{crh::poseidon::constraints::CRHParametersVar, sponge::Absorb};
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use arkworks_small_values_ops::{abs_diff, enforce_in_binary_bound, enforce_in_bound, min};

use crate::{
    circuit_from_step_function,
    sonobe_backend::circuits::arkworks::{
        compression::Pixel,
        input::StepInput,
        ivc_state::{IVCStateT, IVCStateWithInfo},
    },
    transformation::Transformation,
};

fn generate_step_constraints<F: PrimeField + Absorb>(
    cs: ConstraintSystemRef<F>,
    z_i: Vec<FpVar<F>>,
    external_inputs: Vec<FpVar<F>>,
    crh_params: CRHParametersVar<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let state = IVCStateWithInfo::new(z_i);

    let factor = state.info();
    enforce_in_binary_bound::<_, 5>(factor)?;

    let (source_pixels, target_pixels) = external_inputs.two_rows_pixels(cs.clone())?;

    let max = FpVar::Constant(F::from(2550));
    let precision = FpVar::Constant(F::from(10));

    let source = source_pixels
        .iter()
        .flat_map(Pixel::flatten)
        .map(|p| p.mul(factor))
        .map(|scaled| min::<_, 13>(cs.clone(), &scaled, &max));

    let target = target_pixels
        .iter()
        .flat_map(Pixel::flatten)
        .map(|p| p.mul(&precision));

    for (source, target) in source.zip(target) {
        let diff = abs_diff::<_, 13>(cs.clone(), &source?, &target)?;
        enforce_in_bound(&diff, 10)?;
    }

    state.update(&crh_params, &external_inputs)
}

circuit_from_step_function!(Brightness, generate_step_constraints);
