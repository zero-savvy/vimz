use ark_crypto_primitives::{crh::poseidon::constraints::CRHParametersVar, sponge::Absorb};
use ark_ff::PrimeField;
use ark_r1cs_std::{eq::EqGadget, fields::fp::FpVar};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use arkworks_small_values_ops::{abs_diff, min};

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
        let gray = &r_scale * &source.r + &g_scale * &source.g + &b_scale * &source.b;
        let diff = abs_diff::<_, 18>(cs.clone(), &gray, &(target * &full_scale))?;

        // ensure the difference is less than full_scale
        let min_with_scale = min::<_, 18>(cs.clone(), &diff, &full_scale)?;
        min_with_scale.enforce_equal(&diff)?
    }

    state.update(&crh_params, &external_inputs)
}

circuit_from_step_function!(Grayscale, generate_step_constraints);
