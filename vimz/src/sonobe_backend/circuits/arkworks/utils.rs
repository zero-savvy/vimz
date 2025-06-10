use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

use crate::sonobe_backend::circuits::arkworks::compression::{Pixel, decompress_pixels};

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
