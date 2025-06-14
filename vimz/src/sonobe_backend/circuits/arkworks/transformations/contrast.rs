use std::ops::{Add, Mul};

use ark_crypto_primitives::{crh::poseidon::constraints::CRHParametersVar, sponge::Absorb};
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use arkworks_small_values_ops::{
    abs_diff, enforce_in_binary_bound, enforce_in_bound, min, saturating_sub,
};

use crate::{
    circuit_from_step_function,
    sonobe_backend::circuits::arkworks::{
        compression::Pixel,
        step_input::StepInput,
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

    // Ensure the factor is in the range [0, 31]
    let factor = state.info();
    enforce_in_binary_bound::<_, 5>(factor)?;

    let (source_pixels, target_pixels) = external_inputs.as_two_rows_pixels(cs.clone())?;

    let max = FpVar::Constant(F::from(2550));
    let precision = FpVar::Constant(F::from(10));
    let mean = FpVar::Constant(F::from(128));
    let mean_scaled = (&mean).mul(&precision);

    let source = source_pixels.iter().flat_map(Pixel::flatten);

    let target = target_pixels
        .iter()
        .flat_map(Pixel::flatten)
        .map(|p| p.mul(&precision));

    let factor_times_mean = factor.mul(&mean);

    for (source, target) in source.zip(target) {
        // we have to compute (source-128) * factor + 1280 and trim it to [0, 2550]
        // to avoid underflow issues, we do it in the following steps:
        // 1. compute a = source * factor + 1280
        // 2. compute b = a.saturating_sub(factor * 128)
        // 3. take min(b, 2550)
        let a = source.mul(factor).add(&mean_scaled);

        // BIT BOUND: Max value of `a` is 255 · 31 + 1280 < 2^(5 + 8) + 2^11 => 14 bits
        // BIT BOUND: Max value of `factor_times_mean` is 31 · 128 < 2^(5 + 7) => 12 bits
        let b = saturating_sub::<_, 14>(cs.clone(), &a, &factor_times_mean)?;

        // BIT BOUND: Max value of `b` is 255·factor + 1280 - 128·factor <= 127·31 + 1280 < 2^13 => 13 bits
        // BIT BOUND: Max value of `max` is 2550 < 2^12 => 12 bits
        let contrasted = min::<_, 13>(cs.clone(), &b, &max)?;

        // BIT BOUND: `contrasted` is bounded by `b` and `max` => 13 bits
        // BIT BOUND: Max value of `target` is 2550 < 2^12 => 12 bits
        let diff = abs_diff::<_, 13>(cs.clone(), &contrasted, &target)?;
        enforce_in_bound(&diff, 10)?;
    }

    state.update(&crh_params, &external_inputs)
}

circuit_from_step_function!(Contrast, generate_step_constraints);
