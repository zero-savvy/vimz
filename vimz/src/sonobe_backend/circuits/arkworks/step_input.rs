#![allow(clippy::type_complexity)]

use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

use crate::sonobe_backend::circuits::arkworks::{
    compression::{decompress_grayscale, decompress_pixels, unpack},
    pixel::Pixel,
};

pub trait StepInput<F: PrimeField> {
    fn as_two_rows_compressed(&self) -> (&[FpVar<F>], &[FpVar<F>]);

    fn as_two_rows_pixels(
        &self,
        cs: ConstraintSystemRef<F>,
    ) -> Result<(Vec<Pixel<F>>, Vec<Pixel<F>>), SynthesisError>;

    fn as_single_row_unpacked(
        &self,
        cs: ConstraintSystemRef<F>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError>;

    fn as_pixel_row_grayscale_row(
        &self,
        cs: ConstraintSystemRef<F>,
    ) -> Result<(Vec<Pixel<F>>, Vec<FpVar<F>>), SynthesisError>;

    fn as_row_batch_and_row_compressed<const BATCH_SIZE: usize>(
        &self,
    ) -> (Vec<&[FpVar<F>]>, &[FpVar<F>]);

    fn as_convolution_pixels<const KERNEL_SIZE: usize>(
        &self,
        cs: ConstraintSystemRef<F>,
    ) -> Result<(Vec<Vec<Pixel<F>>>, Vec<Pixel<F>>), SynthesisError>;

    fn as_resize_pixels<
        const SOURCE_ROW_WIDTH: usize,
        const SOURCE_ROWS: usize,
        const TARGET_ROW_WIDTH: usize,
        const TARGET_ROWS: usize,
    >(
        &self,
        cs: ConstraintSystemRef<F>,
    ) -> Result<(Vec<Vec<Pixel<F>>>, Vec<Vec<Pixel<F>>>), SynthesisError>;

    fn as_resize_compressed<
        const SOURCE_ROW_WIDTH: usize,
        const SOURCE_ROWS: usize,
        const TARGET_ROW_WIDTH: usize,
        const TARGET_ROWS: usize,
    >(
        &self,
    ) -> Result<(Vec<&[FpVar<F>]>, Vec<&[FpVar<F>]>), SynthesisError>;
}

impl<F: PrimeField> StepInput<F> for Vec<FpVar<F>> {
    fn as_two_rows_compressed(&self) -> (&[FpVar<F>], &[FpVar<F>]) {
        assert_eq!(self.len() % 2, 0);
        (&self[..self.len() / 2], &self[self.len() / 2..])
    }

    fn as_two_rows_pixels(
        &self,
        cs: ConstraintSystemRef<F>,
    ) -> Result<(Vec<Pixel<F>>, Vec<Pixel<F>>), SynthesisError> {
        assert_eq!(self.len() % 2, 0);
        Ok((
            decompress_row(cs.clone(), &self[..self.len() / 2])?,
            decompress_row(cs, &self[self.len() / 2..])?,
        ))
    }

    fn as_single_row_unpacked(
        &self,
        cs: ConstraintSystemRef<F>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        Ok(map_row(cs, self, unpack)?.concat())
    }

    fn as_pixel_row_grayscale_row(
        &self,
        cs: ConstraintSystemRef<F>,
    ) -> Result<(Vec<Pixel<F>>, Vec<FpVar<F>>), SynthesisError> {
        assert_eq!(self.len() % 2, 0);
        Ok((
            decompress_row(cs.clone(), &self[..self.len() / 2])?,
            decompress_gray_row(cs, &self[self.len() / 2..])?,
        ))
    }

    fn as_row_batch_and_row_compressed<const BATCH_SIZE: usize>(
        &self,
    ) -> (Vec<&[FpVar<F>]>, &[FpVar<F>]) {
        let row_width = self.len() / (BATCH_SIZE + 1);
        assert_eq!(self.len() % row_width, 0);
        let batch_rows = self.chunks(row_width).take(BATCH_SIZE).collect::<Vec<_>>();
        (batch_rows, &self[BATCH_SIZE * row_width..])
    }

    fn as_convolution_pixels<const KERNEL_SIZE: usize>(
        &self,
        cs: ConstraintSystemRef<F>,
    ) -> Result<(Vec<Vec<Pixel<F>>>, Vec<Pixel<F>>), SynthesisError> {
        let row_width = self.len() / (KERNEL_SIZE + 1);
        assert_eq!(self.len() % row_width, 0);

        let source_rows = self.chunks(row_width).take(KERNEL_SIZE).collect::<Vec<_>>();
        Ok((
            decompress_convolution_rows::<_, KERNEL_SIZE>(cs.clone(), &source_rows)?,
            decompress_row(cs, &self[KERNEL_SIZE * row_width..])?,
        ))
    }

    fn as_resize_pixels<
        const SOURCE_ROW_WIDTH: usize,
        const SOURCE_ROWS: usize,
        const TARGET_ROW_WIDTH: usize,
        const TARGET_ROWS: usize,
    >(
        &self,
        cs: ConstraintSystemRef<F>,
    ) -> Result<(Vec<Vec<Pixel<F>>>, Vec<Vec<Pixel<F>>>), SynthesisError> {
        assert_eq!(
            self.len(),
            SOURCE_ROW_WIDTH * SOURCE_ROWS + TARGET_ROW_WIDTH * TARGET_ROWS
        );
        let source_rows = self[..SOURCE_ROW_WIDTH * SOURCE_ROWS]
            .chunks(SOURCE_ROW_WIDTH)
            .map(|row| decompress_row(cs.clone(), row))
            .collect::<Result<Vec<_>, _>>()?;
        let target_rows = self[SOURCE_ROW_WIDTH * SOURCE_ROWS..]
            .chunks(TARGET_ROW_WIDTH)
            .map(|row| decompress_row(cs.clone(), row))
            .collect::<Result<Vec<_>, _>>()?;
        Ok((source_rows, target_rows))
    }

    fn as_resize_compressed<
        const SOURCE_ROW_WIDTH: usize,
        const SOURCE_ROWS: usize,
        const TARGET_ROW_WIDTH: usize,
        const TARGET_ROWS: usize,
    >(
        &self,
    ) -> Result<(Vec<&[FpVar<F>]>, Vec<&[FpVar<F>]>), SynthesisError> {
        assert_eq!(
            self.len(),
            SOURCE_ROW_WIDTH * SOURCE_ROWS + TARGET_ROW_WIDTH * TARGET_ROWS
        );
        let source_rows = self[..SOURCE_ROW_WIDTH * SOURCE_ROWS]
            .chunks(SOURCE_ROW_WIDTH)
            .collect::<Vec<_>>();
        let target_rows = self[SOURCE_ROW_WIDTH * SOURCE_ROWS..]
            .chunks(TARGET_ROW_WIDTH)
            .collect::<Vec<_>>();
        Ok((source_rows, target_rows))
    }
}

fn decompress_row<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    row: &[FpVar<F>],
) -> Result<Vec<Pixel<F>>, SynthesisError> {
    Ok(map_row(cs, row, decompress_pixels)?.concat())
}

fn decompress_convolution_rows<F: PrimeField, const KERNEL_SIZE: usize>(
    cs: ConstraintSystemRef<F>,
    rows: &Vec<&[FpVar<F>]>,
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

fn decompress_gray_row<F: PrimeField>(
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
