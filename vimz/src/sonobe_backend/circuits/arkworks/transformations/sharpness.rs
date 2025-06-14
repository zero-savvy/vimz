use std::array;

use ark_crypto_primitives::{crh::poseidon::constraints::CRHParametersVar, sponge::Absorb};
use ark_ff::PrimeField;
use ark_r1cs_std::{eq::EqGadget, fields::fp::FpVar};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use arkworks_small_values_ops::{max, min};

use crate::{
    circuit_from_step_function,
    sonobe_backend::circuits::arkworks::{
        step_input::StepInput,
        ivc_state::{IVCStateConvolution, IVCStateT},
        kernel::{Kernel, KernelEntry},
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
        external_inputs.as_convolution_pixels::<KERNEL_SIZE>(cs.clone())?;

    // Instantiate the sharpness kernel.
    let kernel = sharpness_kernel::<F>();
    // This is the max value of a pixel in the input image.
    let pixel_max_value = FpVar::Constant(F::from(255));
    // This is the offset we need to add to the convolution result to ensure it is non-negative.
    let shift = kernel.abs_min_convolution_value(&pixel_max_value);

    for (i, target_pixel) in target_pixels.iter().enumerate() {
        for color in 0..3 {
            let input = array::from_fn(|row| {
                array::from_fn(|col| source_pixels[row][col + i][color].clone())
            });
            let convolution = kernel.convolve(&input);
            let adjusted = convolution + shift.clone();

            // BIT BOUND: Max value of `adjusted` is `kernel.max_convolution_value` + `shift` < 2^(8+3) + 2^(8+3) => 11 bits
            // BIT BOUND: Max value of `shift + pixel_max_value` is 2^(8 + 3) + 2^8 => 11 bits
            let trimmed_from_up =
                min::<_, 11>(cs.clone(), &adjusted, &(shift.clone() + &pixel_max_value))?;
            // BIT BOUND: `trimmed_from_up` needs 11 bits (operation above)
            // BIT BOUND: `shift` needs no more bits than `shift+pixel_max_value` (operation above) => 11 bits
            let trimmed = max::<_, 11>(cs.clone(), &trimmed_from_up, &shift)?;

            trimmed.enforce_equal(&(&target_pixel[color] + &shift))?
        }
    }

    state.update(&crh_params, &external_inputs)
}

circuit_from_step_function!(Sharpness, generate_step_constraints);

/// [  0, -1,  0 ]
/// [ -1,  5, -1 ]
/// [  0, -1,  0 ]
fn sharpness_kernel<F: PrimeField>() -> Kernel<F, KERNEL_SIZE> {
    Kernel::new([
        [
            KernelEntry::Zero,
            KernelEntry::negative(F::one()),
            KernelEntry::Zero,
        ],
        [
            KernelEntry::negative(F::one()),
            KernelEntry::positive(F::from(5)),
            KernelEntry::negative(F::one()),
        ],
        [
            KernelEntry::Zero,
            KernelEntry::negative(F::one()),
            KernelEntry::Zero,
        ],
    ])
}
