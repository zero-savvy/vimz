use std::ops::Index;

use ark_ff::PrimeField;
use ark_r1cs_std::fields::{FieldVar, fp::FpVar};

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

    pub fn compress(&self) -> FpVar<F> {
        (&self.r)
            + (&self.g) * FpVar::constant(F::from(2).pow([8]))
            + (&self.b) * FpVar::constant(F::from(2).pow([16]))
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
