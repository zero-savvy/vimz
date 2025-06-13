use std::ops::Mul;

use ark_crypto_primitives::{crh::poseidon::constraints::CRHParametersVar, sponge::Absorb};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    eq::EqGadget,
    fields::{FieldVar, fp::FpVar},
};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use arkworks_small_values_ops::{max, min};

use crate::{
    circuit_from_step_function,
    sonobe_backend::circuits::arkworks::{
        input::StepInput,
        ivc_state::{IVCStateConvolution, IVCStateT},
    },
    transformation::Transformation,
};

const KERNEL_SIZE: usize = 3;

fn generate_step_constraints<F: PrimeField + Absorb>(
    cs: ConstraintSystemRef<F>,
    z_i: Vec<FpVar<F>>,
    external_inputs: Vec<FpVar<F>>,
    crh_params: CRHParametersVar<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let state = IVCStateConvolution::<_, KERNEL_SIZE>::new(z_i);

    let (source_pixels, target_pixels) =
        external_inputs.convolution_pixels::<KERNEL_SIZE>(cs.clone())?;

    let kernel = sharpness_kernel::<F>();

    for (i, target_pixel) in target_pixels.iter().enumerate() {
        for color in 0..3 {
            let mut convolution = FpVar::zero();

            for (row_id, source_row) in source_pixels.iter().enumerate() {
                for j in 0..KERNEL_SIZE {
                    // todo: exclude zeros
                    convolution += (&source_row[i + j][color]).mul(&kernel[row_id][j]);
                }
            }

            let adjusted = convolution + FpVar::Constant(F::from(4 * 255));
            // BIT BOUND: Max value of `adjusted` is 255 · 9 < 2^(8 + 4) => 12 bits
            // BIT BOUND: 5 · 255 < 2^11 => 11 bits
            let trimmed = min::<_, 12>(cs.clone(), &adjusted, &FpVar::Constant(F::from(5 * 255)))?;
            // BIT BOUND: Max value of `trimmed` is 255 · 5 < 2^(8 + 3) => 11 bits
            // BIT BOUND: 4 · 255 < 2^10 => 10 bits
            let trimmed = max::<_, 11>(cs.clone(), &trimmed, &FpVar::Constant(F::from(4 * 255)))?;

            trimmed.enforce_equal(&(&target_pixel[color] + FpVar::Constant(F::from(4 * 255))))?
        }
    }

    state.update(&crh_params, &external_inputs)
}

circuit_from_step_function!(Sharpness, generate_step_constraints);

/// Returns a 3x3 kernel for the sharpness transformation.
///
/// The kernel is defined as:
///  [  0, -1,  0 ]
///  [ -1,  5, -1 ]
///  [  0, -1,  0 ]
fn sharpness_kernel<F: PrimeField>() -> [[FpVar<F>; KERNEL_SIZE]; KERNEL_SIZE] {
    [
        [
            FpVar::zero(),
            FpVar::Constant(F::one().neg()),
            FpVar::zero(),
        ],
        [
            FpVar::Constant(F::one().neg()),
            FpVar::Constant(F::from(5)),
            FpVar::Constant(F::one().neg()),
        ],
        [
            FpVar::zero(),
            FpVar::Constant(F::one().neg()),
            FpVar::zero(),
        ],
    ]
}
