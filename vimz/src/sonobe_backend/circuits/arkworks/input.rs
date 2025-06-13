#![allow(clippy::type_complexity)]

use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

use crate::sonobe_backend::circuits::arkworks::compression::{
    Pixel, decompress_convolution_rows, decompress_gray_row, decompress_row,
};

pub trait StepInput<F: PrimeField> {
    fn two_rows_compressed(&self) -> (&[FpVar<F>], &[FpVar<F>]);

    fn two_rows_pixels(
        &self,
        cs: ConstraintSystemRef<F>,
    ) -> Result<(Vec<Pixel<F>>, Vec<Pixel<F>>), SynthesisError>;

    fn pixel_row_grayscale_row(
        &self,
        cs: ConstraintSystemRef<F>,
    ) -> Result<(Vec<Pixel<F>>, Vec<FpVar<F>>), SynthesisError>;

    fn row_batch_and_row_compressed<const BATCH_SIZE: usize>(
        &self,
    ) -> (Vec<&[FpVar<F>]>, &[FpVar<F>]);

    fn convolution_pixels<const KERNEL_SIZE: usize>(
        &self,
        cs: ConstraintSystemRef<F>,
    ) -> Result<(Vec<Vec<Pixel<F>>>, Vec<Pixel<F>>), SynthesisError>;
}

impl<F: PrimeField> StepInput<F> for Vec<FpVar<F>> {
    fn two_rows_compressed(&self) -> (&[FpVar<F>], &[FpVar<F>]) {
        assert_eq!(self.len() % 2, 0);
        (&self[..self.len() / 2], &self[self.len() / 2..])
    }

    fn two_rows_pixels(
        &self,
        cs: ConstraintSystemRef<F>,
    ) -> Result<(Vec<Pixel<F>>, Vec<Pixel<F>>), SynthesisError> {
        assert_eq!(self.len() % 2, 0);
        Ok((
            decompress_row(cs.clone(), &self[..self.len() / 2])?,
            decompress_row(cs, &self[self.len() / 2..])?,
        ))
    }

    fn pixel_row_grayscale_row(
        &self,
        cs: ConstraintSystemRef<F>,
    ) -> Result<(Vec<Pixel<F>>, Vec<FpVar<F>>), SynthesisError> {
        assert_eq!(self.len() % 2, 0);
        Ok((
            decompress_row(cs.clone(), &self[..self.len() / 2])?,
            decompress_gray_row(cs, &self[self.len() / 2..])?,
        ))
    }

    fn row_batch_and_row_compressed<const BATCH_SIZE: usize>(
        &self,
    ) -> (Vec<&[FpVar<F>]>, &[FpVar<F>]) {
        let row_width = self.len() / (BATCH_SIZE + 1);
        assert_eq!(self.len() % row_width, 0);
        let batch_rows = self.chunks(row_width).take(BATCH_SIZE).collect::<Vec<_>>();
        (batch_rows, &self[BATCH_SIZE * row_width..])
    }

    fn convolution_pixels<const KERNEL_SIZE: usize>(
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
}
