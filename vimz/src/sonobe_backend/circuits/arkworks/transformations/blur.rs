use std::{array, ops::Mul};

use ark_crypto_primitives::{crh::poseidon::constraints::CRHParametersVar, sponge::Absorb};
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use arkworks_small_values_ops::{abs_diff, enforce_in_bound};
use array::from_fn;

use crate::{
    circuit_from_step_function,
    sonobe_backend::circuits::arkworks::{
        ivc_state::{IVCStateConvolution, IVCStateT},
        kernel::Kernel,
        step_input::StepInput,
    },
    transformation::Transformation,
};

const KERNEL_SIZE: usize = 3; // Assuming a 3x3 kernel for the blur operation

fn generate_step_constraints<F: PrimeField + Absorb>(
    cs: ConstraintSystemRef<F>,
    z_i: Vec<FpVar<F>>,
    external_inputs: Vec<FpVar<F>>,
    crh_params: CRHParametersVar<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let state = IVCStateConvolution::<_, KERNEL_SIZE>::new(z_i);

    let (source_pixels, target_pixels) =
        external_inputs.as_convolution_pixels::<KERNEL_SIZE>(cs.clone())?;

    let kernel = blur_kernel();
    let kernel_scale = kernel.scale().expect("Blur kernel should be non-negative");

    for (i, target_pixel) in target_pixels.iter().enumerate() {
        for color in 0..3 {
            let conv_input = from_fn(|row| from_fn(|col| &source_pixels[row][col + i][color]));
            let convolution = kernel.convolve(&conv_input);

            let scaled_target = (&target_pixel[color]).mul(FpVar::Constant(F::from(kernel_scale)));
            // BIT BOUND: Max value of `convolution` is 255 · 9 < 2^(8 + 4) => 12 bits
            // BIT BOUND: `scaled_target` has exactly the same bound
            let diff = abs_diff::<_, 12>(cs.clone(), &convolution, &scaled_target)?;
            enforce_in_bound(&diff, kernel_scale)?;
        }
    }

    state.update(&crh_params, &external_inputs)
}

circuit_from_step_function!(Blur, generate_step_constraints);

/// [ 1, 1, 1 ]
/// [ 1, 1, 1 ]
/// [ 1, 1, 1 ]
fn blur_kernel() -> Kernel<KERNEL_SIZE> {
    use crate::sonobe_backend::circuits::arkworks::kernel::KernelEntry::Positive;
    Kernel::new([
        [Positive(1), Positive(1), Positive(1)],
        [Positive(1), Positive(1), Positive(1)],
        [Positive(1), Positive(1), Positive(1)],
    ])
}
