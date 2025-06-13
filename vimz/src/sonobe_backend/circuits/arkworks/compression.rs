use std::ops::Index;

use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{
    R1CSVar,
    alloc::AllocVar,
    eq::EqGadget,
    fields::{FieldVar, fp::FpVar},
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
    pub fn zero() -> Self {
        Pixel {
            r: FpVar::zero(),
            g: FpVar::zero(),
            b: FpVar::zero(),
        }
    }

    pub fn flatten(&self) -> [FpVar<F>; 3] {
        [self.r.clone(), self.g.clone(), self.b.clone()]
    }
}

impl<F: PrimeField> Index<usize> for Pixel<F> {
    type Output = FpVar<F>;

    fn index(&self, index: usize) -> &Self::Output {
        match index {
            0 => &self.r,
            1 => &self.g,
            2 => &self.b,
            _ => panic!("Pixel has only 3 components (r, g, b)"),
        }
    }
}

pub type CompressedPixels<F> = FpVar<F>;
pub type DecomposedPixels<F> = [Pixel<F>; PACKING_FACTOR];

pub fn decompress_row<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    row: &[FpVar<F>],
) -> Result<Vec<Pixel<F>>, SynthesisError> {
    Ok(map_row(cs, row, decompress_pixels)?.concat())
}

pub fn decompress_convolution_rows<F: PrimeField, const KERNEL_SIZE: usize>(
    cs: ConstraintSystemRef<F>,
    rows: &Vec<Vec<FpVar<F>>>,
) -> Result<Vec<Vec<Pixel<F>>>, SynthesisError> {
    assert_eq!(rows.len(), KERNEL_SIZE);

    let mut decompressed_rows_for_conv = vec![];
    let zeros = vec![Pixel::zero(); KERNEL_SIZE / 2];

    for compressed_row in rows {
        let decompressed_row = decompress_row(cs.clone(), compressed_row)?;
        decompressed_rows_for_conv.push([zeros.clone(), decompressed_row, zeros.clone()].concat());
    }
    Ok(decompressed_rows_for_conv)
}

pub fn decompress_gray_row<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    row: &[FpVar<F>],
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    Ok(map_row(cs, row, decompress_grayscale)?.concat())
}

fn map_row<F: PrimeField, T>(
    cs: ConstraintSystemRef<F>,
    row: &[FpVar<F>],
    action: impl Fn(ConstraintSystemRef<F>, &FpVar<F>) -> Result<T, SynthesisError>,
) -> Result<Vec<T>, SynthesisError> {
    row.iter()
        .map(|f| action(cs.clone(), f))
        .collect::<Result<Vec<_>, _>>()
}

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

pub fn decompress_grayscale<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    compressed: &CompressedPixels<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let mut pixels = vec![];

    let bytes = compressed
        .value()
        .map(|raw_value| raw_value.into_bigint().to_bytes_le());

    for i in 0..PACKING_FACTOR {
        pixels.push(FpVar::new_witness(cs.clone(), || {
            Ok(F::from(bytes.clone()?[3 * i]))
        })?);
    }

    let actual_compression = compress_grayscale_pixels(&pixels);
    actual_compression.enforce_equal(compressed)?;

    Ok(pixels)
}

fn compress_grayscale_pixels<F: PrimeField>(pixels: &[FpVar<F>]) -> CompressedPixels<F> {
    let mut compressed = FpVar::zero();

    for (i, pixel) in pixels.iter().enumerate() {
        compressed += pixel * FpVar::constant(F::from(2).pow([3 * 8 * i as u64]));
    }

    compressed
}
