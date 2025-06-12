use std::ops::{Add, Mul, Sub};

use ark_crypto_primitives::{crh::poseidon::constraints::CRHParametersVar, sponge::Absorb};
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use arkworks_small_values_ops::{abs_diff, enforce_in_binary_bound, enforce_in_bound, min};

use crate::{
    circuit_from_step_function,
    sonobe_backend::circuits::arkworks::{
        compression::{Pixel, decompress_row},
        ivc_state::{IVCStateT, IVCStateWithInfo},
    },
    transformation::{Transformation, Transformation::Contrast},
};

const ROW_WIDTH: usize = Contrast.step_input_width();

fn generate_step_constraints<F: PrimeField + Absorb>(
    cs: ConstraintSystemRef<F>,
    z_i: Vec<FpVar<F>>,
    external_inputs: Vec<FpVar<F>>,
    crh_params: CRHParametersVar<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let state = IVCStateWithInfo::new(z_i);

    let factor = state.info();
    enforce_in_binary_bound::<_, 5>(factor)?;

    let source_row = external_inputs[..ROW_WIDTH / 2].to_vec();
    let target_row = external_inputs[ROW_WIDTH / 2..].to_vec();

    let source_pixels = decompress_row(cs.clone(), &source_row)?;
    let target_pixels = decompress_row(cs.clone(), &target_row)?;

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
        // we have to compute (source-128) * factor + 1280 and clamp it to [0, 2550]
        // to avoid underflow issues, we do it in the following steps:
        // 1. compute a = source * factor + 1280
        // 2. compute b = a - factor * 128         clamped to [0, ...)
        // 3. take min(b, 2550)
        let a = source.mul(factor).add(&mean_scaled); // source * factor + 1280
        let to_subtract = min::<_, 14>(cs.clone(), &a, &factor_times_mean)?;
        let b = a.sub(&to_subtract); // a - factor * 128
        let contrasted = min::<_, 13>(cs.clone(), &b, &max)?;

        let diff = abs_diff::<_, 13>(cs.clone(), &contrasted, &target)?;
        enforce_in_bound(&diff, 10)?;
    }

    state.update(&crh_params, &source_row, &target_row)
}

circuit_from_step_function!(Contrast, generate_step_constraints);
