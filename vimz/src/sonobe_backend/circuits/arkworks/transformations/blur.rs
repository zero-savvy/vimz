use std::ops::Mul;

use ark_crypto_primitives::{crh::poseidon::constraints::CRHParametersVar, sponge::Absorb};
use ark_ff::PrimeField;
use ark_r1cs_std::fields::{FieldVar, fp::FpVar};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use arkworks_small_values_ops::{abs_diff, enforce_in_bound};

use crate::{
    circuit_from_step_function,
    sonobe_backend::circuits::arkworks::{
        compression::{decompress_convolution_rows, decompress_row},
        ivc_state::{IVCStateConvolution, IVCStateT},
    },
    transformation::{Transformation, Transformation::Blur},
};

const KERNEL_SIZE: usize = 3; // Assuming a 3x3 kernel for the blur operation
const ROW_WIDTH: usize = Blur.step_input_width() / (KERNEL_SIZE + 1);
const KERNEL_WEIGHT: usize = KERNEL_SIZE * KERNEL_SIZE;

fn generate_step_constraints<F: PrimeField + Absorb>(
    cs: ConstraintSystemRef<F>,
    z_i: Vec<FpVar<F>>,
    external_inputs: Vec<FpVar<F>>,
    crh_params: CRHParametersVar<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let state = IVCStateConvolution::<_, KERNEL_SIZE>::new(z_i);

    let mut source_rows = vec![];
    for i in 0..KERNEL_SIZE {
        source_rows.push(external_inputs[i * ROW_WIDTH..(i + 1) * ROW_WIDTH].to_vec());
    }
    let target_row = external_inputs[KERNEL_SIZE * ROW_WIDTH..].to_vec();

    let source_pixels = decompress_convolution_rows::<_, KERNEL_SIZE>(cs.clone(), &source_rows)?;
    let target_pixels = decompress_row(cs.clone(), &target_row)?;

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
            let diff = abs_diff::<_, 12>(cs.clone(), &convolution, &scaled_target)?;
            enforce_in_bound(&diff, KERNEL_WEIGHT as u8)?;
        }
    }

    state.update(&crh_params, &source_rows.try_into().unwrap(), &target_row)
}

circuit_from_step_function!(Blur, generate_step_constraints);
