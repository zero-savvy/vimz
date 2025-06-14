use std::ops::Mul;

use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;

pub struct Kernel<const KERNEL_SIZE: usize> {
    kernel: [[KernelEntry<u8>; KERNEL_SIZE]; KERNEL_SIZE],
}

impl<const KERNEL_SIZE: usize> Kernel<KERNEL_SIZE> {
    pub const fn new(kernel: [[KernelEntry<u8>; KERNEL_SIZE]; KERNEL_SIZE]) -> Self {
        Self { kernel }
    }

    pub fn convolve<F: PrimeField>(
        &self,
        input: &[[&FpVar<F>; KERNEL_SIZE]; KERNEL_SIZE],
    ) -> FpVar<F> {
        let mut result = FpVar::Constant(F::zero());
        for (i, input_row) in input.iter().enumerate() {
            for (j, input_value) in input_row.iter().enumerate() {
                match &self.kernel[i][j] {
                    KernelEntry::Positive(k) => {
                        result += input_value.mul(FpVar::Constant(F::from(*k)));
                    }
                    KernelEntry::Negative(k) => {
                        result -= input_value.mul(FpVar::Constant(F::from(*k)));
                    }
                    KernelEntry::Zero => {}
                }
            }
        }
        result
    }

    pub fn scale(&self) -> Option<u8> {
        let mut scale = 0u8;
        for i in 0..KERNEL_SIZE {
            for j in 0..KERNEL_SIZE {
                match self.kernel[i][j] {
                    KernelEntry::Positive(k) => {
                        scale = scale.checked_add(k).expect("Overflow in kernel scaling");
                    }
                    KernelEntry::Negative(k) => {
                        assert_ne!(k, 0, "Negative kernel entry cannot be zero");
                        return None;
                    }
                    KernelEntry::Zero => {}
                }
            }
        }
        Some(scale)
    }

    pub fn abs_min_convolution_value<F: PrimeField>(&self, max_input_value: &FpVar<F>) -> FpVar<F> {
        let mut min_value = 0;
        for i in 0..KERNEL_SIZE {
            for j in 0..KERNEL_SIZE {
                if let KernelEntry::Negative(k) = &self.kernel[i][j] {
                    min_value += k;
                }
            }
        }
        FpVar::Constant(F::from(min_value)) * max_input_value
    }
}

#[derive(Copy, Clone, Debug)]
pub enum KernelEntry<T> {
    Positive(T),
    Zero,
    Negative(T),
}
