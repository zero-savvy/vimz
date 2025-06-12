use Transformation::Grayscale;
use ark_crypto_primitives::{crh::poseidon::constraints::CRHParametersVar, sponge::Absorb};
use ark_ff::PrimeField;
use ark_r1cs_std::{eq::EqGadget, fields::fp::FpVar};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use arkworks_small_values_ops::{abs_diff, min};

use crate::{
    circuit_from_step_function,
    sonobe_backend::circuits::arkworks::{
        compression::{decompress_gray_row, decompress_row},
        ivc_state::{IVCState, IVCStateT},
    },
    transformation::Transformation,
};

const ROW_WIDTH: usize = Grayscale.step_input_width();

fn generate_step_constraints<F: PrimeField + Absorb>(
    cs: ConstraintSystemRef<F>,
    z_i: Vec<FpVar<F>>,
    external_inputs: Vec<FpVar<F>>,
    crh_params: CRHParametersVar<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let state = IVCState::new(z_i);

    let source_row = external_inputs[..ROW_WIDTH / 2].to_vec();
    let target_row = external_inputs[ROW_WIDTH / 2..].to_vec();

    let source_pixels = decompress_row(cs.clone(), &source_row)?;
    let target_pixels = decompress_gray_row(cs.clone(), &target_row)?;

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

    state.update(&crh_params, &source_row, &target_row)
}

circuit_from_step_function!(Grayscale, generate_step_constraints);
