use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{
    alloc::AllocVar,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    R1CSVar,
};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

pub const PACKING_FACTOR: usize = 10;

#[derive(Clone, Debug)]
pub struct Pixel<F: PrimeField> {
    pub r: FpVar<F>,
    pub g: FpVar<F>,
    pub b: FpVar<F>,
}

impl<F: PrimeField> Pixel<F> {
    pub fn flatten(&self) -> [FpVar<F>; 3] {
        [self.r.clone(), self.g.clone(), self.b.clone()]
    }
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

fn compress_pixels<F: PrimeField>(pixels: &[Pixel<F>]) -> CompressedPixels<F> {
    let mut compressed = FpVar::zero();

    for (i, pixel) in pixels.iter().enumerate() {
        let offset = i * 3;
        compressed += &pixel.r * FpVar::constant(F::from(2).pow([8 * offset as u64]));
        compressed += &pixel.g * FpVar::constant(F::from(2).pow([8 * (offset + 1) as u64]));
        compressed += &pixel.b * FpVar::constant(F::from(2).pow([8 * (offset + 2) as u64]));
    }

    compressed
}
