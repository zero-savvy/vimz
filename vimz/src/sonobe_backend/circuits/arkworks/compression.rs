use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{
    R1CSVar,
    alloc::AllocVar,
    eq::EqGadget,
    fields::{FieldVar, fp::FpVar},
};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

use crate::{PACKING_FACTOR, sonobe_backend::circuits::arkworks::pixel::Pixel};

pub fn decompress_pixels<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    compressed: &FpVar<F>,
) -> Result<[Pixel<F>; PACKING_FACTOR], SynthesisError> {
    let mut pixels = vec![];

    let bytes = to_bytes(compressed);
    for i in 0..PACKING_FACTOR {
        let offset = i * 3;
        let r = FpVar::new_witness(cs.clone(), || Ok(F::from(bytes.clone()?[offset])))?;
        let g = FpVar::new_witness(cs.clone(), || Ok(F::from(bytes.clone()?[offset + 1])))?;
        let b = FpVar::new_witness(cs.clone(), || Ok(F::from(bytes.clone()?[offset + 2])))?;
        pixels.push(Pixel { r, g, b });
    }

    // Reconstruct the compressed value from the decomposed pixels, to ensure that prover's advices
    // are correct.
    let actual_compression = compress_pixels(&pixels);
    actual_compression.enforce_equal(compressed)?;

    Ok(pixels.try_into().unwrap())
}

fn compress_pixels<F: PrimeField>(pixels: &[Pixel<F>]) -> FpVar<F> {
    pixels
        .iter()
        .enumerate()
        .fold(FpVar::zero(), |acc, (i, pixel)| {
            acc + pixel.compress() * FpVar::constant(F::from(2).pow([24 * i as u64]))
        })
}

pub fn decompress_grayscale<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    compressed: &FpVar<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let mut pixels = vec![];

    let bytes = to_bytes(compressed);
    for i in 0..PACKING_FACTOR {
        pixels.push(FpVar::new_witness(cs.clone(), || {
            Ok(F::from(bytes.clone()?[3 * i]))
        })?);
    }

    let actual_compression = pack(&pixels);
    actual_compression.enforce_equal(compressed)?;

    Ok(pixels)
}

pub fn unpack<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    packed: &FpVar<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let mut unpacked = vec![];

    let bytes = to_bytes(packed);
    for i in 0..PACKING_FACTOR {
        unpacked.push(FpVar::new_witness(cs.clone(), || {
            Ok(F::from_le_bytes_mod_order(
                &bytes.clone()?[i * 3..(i * 3) + 3],
            ))
        })?);
    }

    let actual_packing = pack(&unpacked);
    actual_packing.enforce_equal(packed)?;

    Ok(unpacked)
}

pub fn pack<F: PrimeField>(unpacked: &[FpVar<F>]) -> FpVar<F> {
    assert!(unpacked.len() <= PACKING_FACTOR);
    unpacked
        .iter()
        .enumerate()
        .fold(FpVar::zero(), |acc, (i, value)| {
            acc + value * FpVar::constant(F::from(2).pow([24 * i as u64]))
        })
}

fn to_bytes<F: PrimeField>(value: &FpVar<F>) -> Result<Vec<u8>, SynthesisError> {
    value.value().map(|v| v.into_bigint().to_bytes_le())
}
