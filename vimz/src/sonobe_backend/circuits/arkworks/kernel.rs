use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;

pub struct Kernel<F: PrimeField, const KERNEL_SIZE: usize> {
    kernel: [[KernelEntry<F>; KERNEL_SIZE]; KERNEL_SIZE],
}

impl<F: PrimeField, const KERNEL_SIZE: usize> Kernel<F, KERNEL_SIZE> {
    pub fn new(kernel: [[KernelEntry<F>; KERNEL_SIZE]; KERNEL_SIZE]) -> Self {
        Self { kernel }
    }

    pub fn convolve(&self, input: &[[&FpVar<F>; KERNEL_SIZE]; KERNEL_SIZE]) -> FpVar<F> {
        let mut result = FpVar::Constant(F::zero());
        for (i, input_row) in input.iter().enumerate() {
            for (j, input_value) in input_row.iter().enumerate() {
                match &self.kernel[i][j] {
                    KernelEntry::Positive(k) => {
                        result += k * *input_value;
                    }
                    KernelEntry::Negative(k) => {
                        result -= k * *input_value;
                    }
                    KernelEntry::Zero => {}
                }
            }
        }
        result
    }

    pub fn max_convolution_value(&self, max_input_value: &FpVar<F>) -> FpVar<F> {
        let mut max_value = FpVar::Constant(F::zero());
        for i in 0..KERNEL_SIZE {
            for j in 0..KERNEL_SIZE {
                if let KernelEntry::Positive(k) = &self.kernel[i][j] {
                    max_value += k;
                }
            }
        }
        max_value * max_input_value
    }

    pub fn abs_min_convolution_value(&self, max_input_value: &FpVar<F>) -> FpVar<F> {
        let mut min_value = FpVar::Constant(F::zero());
        for i in 0..KERNEL_SIZE {
            for j in 0..KERNEL_SIZE {
                if let KernelEntry::Negative(k) = &self.kernel[i][j] {
                    min_value += k;
                }
            }
        }
        min_value * max_input_value
    }
}

#[derive(Clone, Debug)]
pub enum KernelEntry<F: PrimeField> {
    Positive(FpVar<F>),
    Zero,
    Negative(FpVar<F>),
}

impl<F: PrimeField> KernelEntry<F> {
    pub fn positive(value: F) -> Self {
        KernelEntry::Positive(FpVar::Constant(value))
    }

    pub fn negative(value: F) -> Self {
        KernelEntry::Negative(FpVar::Constant(value))
    }
}
