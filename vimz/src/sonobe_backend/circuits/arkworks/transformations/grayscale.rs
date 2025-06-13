use ark_crypto_primitives::{crh::poseidon::constraints::CRHParametersVar, sponge::Absorb};
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use arkworks_small_values_ops::{abs_diff, enforce_le};

use crate::{
    circuit_from_step_function,
    sonobe_backend::circuits::arkworks::{
        input::StepInput,
        ivc_state::{IVCState, IVCStateT},
    },
    transformation::Transformation,
};

fn generate_step_constraints<F: PrimeField + Absorb>(
    cs: ConstraintSystemRef<F>,
    z_i: Vec<FpVar<F>>,
    external_inputs: Vec<FpVar<F>>,
    crh_params: CRHParametersVar<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let state = IVCState::new(z_i);

    let (source_pixels, target_pixels) = external_inputs.pixel_row_grayscale_row(cs.clone())?;

    let r_scale = FpVar::Constant(F::from(299));
    let g_scale = FpVar::Constant(F::from(587));
    let b_scale = FpVar::Constant(F::from(114));
    let full_scale = FpVar::Constant(F::from(1000));

    for (source, target) in source_pixels.iter().zip(target_pixels.iter()) {
        // 1) Compute the grayscale value as a linear combination of RGB values.
        let gray = &r_scale * &source.r + &g_scale * &source.g + &b_scale * &source.b;

        // 2) Compute the difference between the actual and claimed values.
        // BIT BOUND: Max value of `gray` is 1000 · 255 < 2^(10 + 8) => 18 bits
        // BIT BOUND: Max value of `target` is 1000 · 255 < 2^(10 + 8) => 18 bits
        let diff = abs_diff::<_, 18>(cs.clone(), &gray, &(target * &full_scale))?;

        // 3) Ensure the difference is less than computation precision
        // BIT BOUND: Max value of `diff` is 1000 · 255 < 2^(10 + 8) => 18 bits
        // BIT BOUND: Max value of `full_scale` is 1000 < 2^10 => 10 bits
        enforce_le::<_, 18>(cs.clone(), &diff, &full_scale)?;
    }

    state.update(&crh_params, &external_inputs)
}

circuit_from_step_function!(Grayscale, generate_step_constraints);
