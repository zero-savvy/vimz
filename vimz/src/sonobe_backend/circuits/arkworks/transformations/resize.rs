use ark_crypto_primitives::{crh::poseidon::constraints::CRHParametersVar, sponge::Absorb};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    R1CSVar,
    fields::{FieldVar, fp::FpVar},
};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use arkworks_small_values_ops::{abs_diff, enforce_in_bound};

use crate::{
    circuit_from_step_function,
    sonobe_backend::circuits::arkworks::{
        compression::Pixel,
        ivc_state::{IVCState, IVCStateT},
        kernel::{Kernel, KernelEntry},
        step_input::StepInput,
    },
    transformation::Transformation,
};

fn generate_step_constraints<F: PrimeField + Absorb>(
    cs: ConstraintSystemRef<F>,
    z_i: Vec<FpVar<F>>,
    external_inputs: Vec<FpVar<F>>,
    crh_params: CRHParametersVar<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // !!! The current implementation will work only for resizing 3 rows to 2 rows. !!!
    // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

    let state = IVCState::new(z_i);
    let (source_rows, target_rows) =
        external_inputs.as_resize_pixels::<128, 3, 64, 2>(cs.clone())?;

    interpolate_single_row(
        cs.clone(),
        &source_rows[0],
        &source_rows[1],
        upper_kernel(),
        &target_rows[0],
    )?;
    interpolate_single_row(
        cs.clone(),
        &source_rows[1],
        &source_rows[2],
        lower_kernel(),
        &target_rows[1],
    )?;

    state.update(&crh_params, &external_inputs)
}

circuit_from_step_function!(Resize, generate_step_constraints);

fn interpolate_single_row<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    upper_source_row: &[Pixel<F>],
    lower_source_row: &[Pixel<F>],
    kernel: Kernel<F, 2>,
    target_row: &[Pixel<F>],
) -> Result<(), SynthesisError> {
    assert_eq!(upper_source_row.len(), lower_source_row.len());
    assert_eq!(2 * target_row.len(), upper_source_row.len());

    let scale = kernel.max_convolution_value(&FpVar::one());
    assert_eq!(F::from(6), scale.value().expect("Scale should be constant"));

    for (target_column, target_pixel) in target_row.iter().enumerate() {
        for color in 0..3 {
            let source_contributors = [
                [
                    &upper_source_row[2 * target_column][color],
                    &upper_source_row[2 * target_column + 1][color],
                ],
                [
                    &lower_source_row[2 * target_column][color],
                    &lower_source_row[2 * target_column + 1][color],
                ],
            ];
            let convolution = kernel.convolve(&source_contributors);

            // BIT BOUND: Max value of `convolution` is `scale` · 255 = 1530 < 2 ^ 11 => 11 bits
            // BIT BOUND: `scale · target_pixel[color]` has exactly the same bound
            let diff =
                abs_diff::<_, 11>(cs.clone(), &convolution, &(&scale * &target_pixel[color]))?;

            // It is easier to hardcode the u8 bound here and add an assertion for `scale` above.
            enforce_in_bound(&diff, 6)?;
        }
    }
    Ok(())
}

/// [ 2, 2 ]
/// [ 1, 1 ]
fn upper_kernel<F: PrimeField>() -> Kernel<F, 2> {
    Kernel::new([
        [
            KernelEntry::positive(F::from(2)),
            KernelEntry::positive(F::from(2)),
        ],
        [
            KernelEntry::positive(F::from(1)),
            KernelEntry::positive(F::from(1)),
        ],
    ])
}

/// [ 1, 1 ]
/// [ 2, 2 ]
fn lower_kernel<F: PrimeField>() -> Kernel<F, 2> {
    Kernel::new([
        [
            KernelEntry::positive(F::from(1)),
            KernelEntry::positive(F::from(1)),
        ],
        [
            KernelEntry::positive(F::from(2)),
            KernelEntry::positive(F::from(2)),
        ],
    ])
}
