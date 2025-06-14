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
        ivc_state::{IVCStateT, IVCStateWithInfo},
        step_input::StepInput,
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

    // 1) Ensure the factor is in the range [0, 31]
    let factor = state.info();
    enforce_in_binary_bound::<_, 5>(factor)?;

    let (source_pixels, target_pixels) = external_inputs.as_two_rows_pixels(cs.clone())?;

    let max = FpVar::Constant(F::from(2550));
    let precision = FpVar::Constant(F::from(10));

    // 2) Scale the source pixels by the factor and trim them to 2550
    let actual = source_pixels
        .iter()
        .flat_map(Pixel::flatten)
        .map(|p| p.mul(factor))
        // BIT BOUND: Max value of `scaled` is 31 · 255 < 2^(5+8) => 13 bits
        // BIT BOUND: Max value of `max` is 2550 < 2^12 => 12 bits
        .map(|scaled| min::<_, 13>(cs.clone(), &scaled, &max));

    // 3) Scale the target pixels by the precision
    let target_scaled = target_pixels
        .iter()
        .flat_map(Pixel::flatten)
        .map(|p| p.mul(&precision));

    // 4) Ensure the absolute difference between the scaled source and target pixels is within the precision
    for (actual, claimed) in actual.zip(target_scaled) {
        // BIT BOUND: Max value of `actual` is 2550 < 2^12 => 12 bits
        // BIT BOUND: Max value of `claimed` is 2550 < 2^12 => 12 bits
        let diff = abs_diff::<_, 12>(cs.clone(), &actual?, &claimed)?;
        enforce_in_bound(&diff, 10)?;
    }

    state.update(&crh_params, &external_inputs)
}

circuit_from_step_function!(Brightness, generate_step_constraints);
