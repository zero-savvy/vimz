use std::ops::Mul;

use ark_crypto_primitives::{crh::poseidon::constraints::CRHParametersVar, sponge::Absorb};
use ark_ff::PrimeField;
use ark_r1cs_std::fields::{FieldVar, fp::FpVar};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use arkworks_small_values_ops::{abs_diff, enforce_in_bound};

use crate::{
    circuit_from_step_function,
    sonobe_backend::circuits::arkworks::{
        ivc_state::{IVCStateConvolution, IVCStateT},
        step_input::StepInput,
    },
    transformation::Transformation,
};

const KERNEL_SIZE: usize = 3; // Assuming a 3x3 kernel for the blur operation
const KERNEL_WEIGHT: usize = KERNEL_SIZE * KERNEL_SIZE;

fn generate_step_constraints<F: PrimeField + Absorb>(
    cs: ConstraintSystemRef<F>,
    z_i: Vec<FpVar<F>>,
    external_inputs: Vec<FpVar<F>>,
    crh_params: CRHParametersVar<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let state = IVCStateConvolution::<_, KERNEL_SIZE>::new(z_i);

    let (source_pixels, target_pixels) =
        external_inputs.as_convolution_pixels::<KERNEL_SIZE>(cs.clone())?;

    let kernel_weight = FpVar::Constant(F::from((KERNEL_SIZE * KERNEL_SIZE) as u64));
    for (i, target_pixel) in target_pixels.iter().enumerate() {
        for color in 0..3 {
            let mut convolution = FpVar::zero();

            for source_row in &source_pixels {
                for j in 0..KERNEL_SIZE {
                    convolution += &source_row[i + j][color];
                }
            }

            let scaled_target = (&target_pixel[color]).mul(&kernel_weight);
            // BIT BOUND: Max value of `convolution` is 255 * 9 < 2^(8 + 4) => 12 bits
            // BIT BOUND: Max value of `scaled_target` is 255 * 9 < 2^(8 + 4) => 12 bits
            let diff = abs_diff::<_, 12>(cs.clone(), &convolution, &scaled_target)?;
            enforce_in_bound(&diff, KERNEL_WEIGHT as u8)?;
        }
    }

    state.update(&crh_params, &external_inputs)
}

circuit_from_step_function!(Blur, generate_step_constraints);
