use ark_crypto_primitives::{
    crh::{
        CRHSchemeGadget, TwoToOneCRHSchemeGadget,
        poseidon::constraints::{CRHGadget, CRHParametersVar, TwoToOneCRHGadget},
    },
    sponge::Absorb,
};
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use arkworks_small_values_ops::{abs_diff, enforce_in_bound};

use crate::{
    circuit_from_step_function,
    sonobe_backend::circuits::arkworks::{
        ivc_state::{IVCState, IVCStateT},
        kernel::{Kernel, KernelEntry},
        pixel::Pixel,
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

    update_state(&state, &crh_params, &external_inputs)
}

circuit_from_step_function!(Resize, generate_step_constraints);

fn interpolate_single_row<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    upper_source_row: &[Pixel<F>],
    lower_source_row: &[Pixel<F>],
    kernel: Kernel<2>,
    target_row: &[Pixel<F>],
) -> Result<(), SynthesisError> {
    assert_eq!(upper_source_row.len(), lower_source_row.len());
    assert_eq!(2 * target_row.len(), upper_source_row.len());

    let scale = kernel
        .scale()
        .expect("Interpolation kernel is non-negative");

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
            let diff = abs_diff::<_, 11>(
                cs.clone(),
                &convolution,
                &(FpVar::Constant(F::from(scale)) * &target_pixel[color]),
            )?;

            enforce_in_bound(&diff, scale)?;
        }
    }
    Ok(())
}

/// [ 2, 2 ]
/// [ 1, 1 ]
fn upper_kernel() -> Kernel<2> {
    use KernelEntry::Positive;
    Kernel::new([[Positive(2), Positive(2)], [Positive(1), Positive(1)]])
}

/// [ 1, 1 ]
/// [ 2, 2 ]
fn lower_kernel() -> Kernel<2> {
    use KernelEntry::Positive;
    Kernel::new([[Positive(1), Positive(1)], [Positive(2), Positive(2)]])
}

fn update_state<F: PrimeField + Absorb>(
    state: &IVCState<F>,
    crh_params: &CRHParametersVar<F>,
    input: &impl StepInput<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let (source_rows, target_rows) = input.as_resize_compressed::<128, 3, 64, 2>()?;

    let mut source_hash = state.source_hash.clone();
    for row in source_rows {
        let row_hash = CRHGadget::evaluate(crh_params, row)?;
        source_hash = TwoToOneCRHGadget::<F>::evaluate(crh_params, &source_hash, &row_hash)?;
    }

    let mut target_hash = state.target_hash.clone();
    for row in target_rows {
        let row_hash = CRHGadget::evaluate(crh_params, row)?;
        target_hash = TwoToOneCRHGadget::<F>::evaluate(crh_params, &target_hash, &row_hash)?;
    }

    Ok(vec![source_hash, target_hash])
}
