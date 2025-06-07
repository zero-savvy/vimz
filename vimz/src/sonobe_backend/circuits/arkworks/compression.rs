use ark_ff::{BigInteger, Field, PrimeField};
use ark_r1cs_std::{
    alloc::AllocVar,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    uint8::UInt8,
    R1CSVar,
};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

pub const PACKING_FACTOR: usize = 10;

#[derive(Clone, Debug)]
pub struct Pixel<F: Field> {
    pub r: UInt8<F>,
    pub g: UInt8<F>,
    pub b: UInt8<F>,
}

pub type CompressedPixels<F> = FpVar<F>;
pub type DecomposedPixels<F> = [Pixel<F>; PACKING_FACTOR];

pub fn decompress_pixels<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    compressed: &CompressedPixels<F>,
) -> Result<DecomposedPixels<F>, SynthesisError> {
    let mut pixels = vec![];

    let bytes = compressed
        .value()
        .map(|raw_value| raw_value.into_bigint().to_bytes_le());

    for i in 0..PACKING_FACTOR {
        let offset = i * 3;
        let r = UInt8::new_witness(cs.clone(), || Ok(bytes.clone()?[offset]))?;
        let g = UInt8::new_witness(cs.clone(), || Ok(bytes.clone()?[offset + 1]))?;
        let b = UInt8::new_witness(cs.clone(), || Ok(bytes.clone()?[offset + 2]))?;
        pixels.push(Pixel { r, g, b });
    }

    // Reconstruct the compressed value from the decomposed pixels, to ensure that prover's advices
    // are correct.
    let actual_compression = compress_pixels(cs, &pixels)?;
    actual_compression.enforce_equal(compressed)?;

    Ok(pixels.try_into().unwrap())
}

fn compress_pixels<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    pixels: &[Pixel<F>],
) -> Result<CompressedPixels<F>, SynthesisError> {
    let mut compressed = FpVar::zero();

    for (i, pixel) in pixels.iter().enumerate() {
        let offset = i * 3;
        compressed += pixel.r.to_fp()? * FpVar::constant(F::from(2).pow([8 * offset as u64]));
        compressed += pixel.g.to_fp()? * FpVar::constant(F::from(2).pow([8 * (offset + 1) as u64]));
        compressed += pixel.b.to_fp()? * FpVar::constant(F::from(2).pow([8 * (offset + 2) as u64]));
    }

    Ok(compressed)
}
