use ark_crypto_primitives::{crh::poseidon::constraints::CRHParametersVar, sponge::Absorb};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{R1CSVar, alloc::AllocVar, eq::EqGadget, fields::fp::FpVar};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

use crate::{
    circuit_from_step_function,
    sonobe_backend::circuits::arkworks::{
        ivc_state::{IVCStateT, IVCStateWithInfo},
        step_input::StepInput,
    },
    transformation::Transformation,
};

const CROP_WIDTH: usize = 640;

fn generate_step_constraints<F: PrimeField + Absorb>(
    cs: ConstraintSystemRef<F>,
    z_i: Vec<FpVar<F>>,
    external_inputs: Vec<FpVar<F>>,
    crh_params: CRHParametersVar<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let state = IVCStateWithInfo::new(z_i);
    let info = decode_info(cs.clone(), state.info())?;

    let pixel_row = external_inputs.as_single_row_unpacked(cs.clone())?;
    let subrow = get_subrow(cs.clone(), &pixel_row, &info.crop_col)?;

    state.update(&crh_params, &external_inputs)
}

circuit_from_step_function!(Crop, generate_step_constraints);

struct Info<F: PrimeField> {
    current_row: FpVar<F>,
    crop_row: FpVar<F>,
    crop_col: FpVar<F>,
}

fn decode_info<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    encoded: &FpVar<F>,
) -> Result<Info<F>, SynthesisError> {
    // 1) Compute the decoded witness values.
    let bits = encoded
        .value()
        .map(|raw_value| raw_value.into_bigint().to_bits_le());

    let current_row = FpVar::new_witness(cs.clone(), || {
        F::from_bigint(<F::BigInt>::from_bits_le(&bits.clone()?[0..12]))
            .ok_or(SynthesisError::Unsatisfiable)
    })?;
    let crop_row = FpVar::new_witness(cs.clone(), || {
        F::from_bigint(<F::BigInt>::from_bits_le(&bits.clone()?[12..24]))
            .ok_or(SynthesisError::Unsatisfiable)
    })?;
    let crop_col = FpVar::new_witness(cs.clone(), || {
        F::from_bigint(<F::BigInt>::from_bits_le(&bits?[24..36]))
            .ok_or(SynthesisError::Unsatisfiable)
    })?;

    // 2) Ensure integrity.
    let reconstructed = crop_col.clone() * FpVar::Constant(F::from(2).pow([24]))
        + crop_row.clone() * FpVar::Constant(F::from(2).pow([12]))
        + current_row.clone();
    reconstructed.enforce_equal(encoded)?;

    // 3) Return the info struct.
    Ok(Info {
        current_row,
        crop_row,
        crop_col,
    })
}

fn get_subrow<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    row: &[FpVar<F>],
    crop_index: &FpVar<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    // 1) Prepare variables and set them to actual values. -----------------------------------------

    // 1.1) Cast the `crop_index` from `FpVar` to `usize`.
    let crop_index_usize = crop_index.value().map(|i| {
        let bytes = i.into_bigint().to_bytes_le();
        u64::from_le_bytes(bytes[..8].to_vec().try_into().unwrap()) as usize
    });

    // 1.2) Provide a witness for the subrow.
    let mut subrow = vec![];
    for i in 0..CROP_WIDTH {
        let index = crop_index_usize.map(|idx| idx + i);
        subrow.push(FpVar::new_witness(cs.clone(), || row[index?].value())?);
    }

    // 2) Add constraints to ensure that the subrow is valid. --------------------------------------

    Ok(subrow)
}
