use std::cmp::Ordering;

use ark_ff::PrimeField;
use ark_r1cs_std::{cmp::CmpGadget, fields::fp::FpVar, uint16::UInt16};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

use crate::sonobe_backend::circuits::arkworks::compression::{decompress_pixels, Pixel};

pub fn decompress_row<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    row: &[FpVar<F>],
) -> Result<Vec<Pixel<F>>, SynthesisError> {
    Ok(row
        .iter()
        .map(|f| decompress_pixels(cs.clone(), f))
        .collect::<Result<Vec<_>, _>>()?
        .concat())
}

pub fn cap<F: PrimeField>(value: &UInt16<F>, max: &UInt16<F>) -> Result<UInt16<F>, SynthesisError> {
    value.is_lt(max)?.select(&value, &max)
}

pub fn abs_diff<F: PrimeField>(a: &FpVar<F>, b: &FpVar<F>) -> Result<FpVar<F>, SynthesisError> {
    a.is_cmp(b, Ordering::Less, false)?
        .select(&(b - a), &(a - b))
}
