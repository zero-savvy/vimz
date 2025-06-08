use std::ops::Mul;

use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{
    alloc::AllocVar,
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    R1CSVar,
};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

use crate::sonobe_backend::circuits::arkworks::compression::{decompress_pixels, Pixel};

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

pub fn cap<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    a: &FpVar<F>,
    max: &FpVar<F>,
) -> Result<FpVar<F>, SynthesisError> {
    let a_v = a.value();
    let max_v = max.value();

    let b = FpVar::new_witness(cs.clone(), || {
        if a_v? > max_v? {
            Ok(a_v? - max_v?)
        } else {
            Ok(F::zero())
        }
    })?;
    let b_bits = (0..13)
        .map(|i| Boolean::new_witness(cs.clone(), || Ok(b.value()?.into_bigint().get_bit(i))))
        .collect::<Result<Vec<_>, _>>()?;

    let c = FpVar::new_witness(cs.clone(), || {
        if a_v? < max_v? {
            Ok(max_v? - a_v?)
        } else {
            Ok(F::zero())
        }
    })?;
    let c_bits = (0..13)
        .map(|i| Boolean::new_witness(cs.clone(), || Ok(c.value()?.into_bigint().get_bit(i))))
        .collect::<Result<Vec<_>, _>>()?;

    b.clone().mul(&c).is_zero()?.enforce_equal(&Boolean::TRUE)?;

    let mut b_from_bits = FpVar::Constant(F::zero());
    for (i, bit) in b_bits.iter().enumerate() {
        b_from_bits += FpVar::from(bit.clone()) * FpVar::Constant(F::from(1u64 << i));
    }
    b_from_bits.enforce_equal(&b)?;

    let mut c_from_bits = FpVar::Constant(F::zero());
    for (i, bit) in c_bits.iter().enumerate() {
        c_from_bits += FpVar::from(bit.clone()) * FpVar::Constant(F::from(1u64 << i));
    }
    c_from_bits.enforce_equal(&c)?;

    (a - b.clone() + c - max)
        .is_zero()?
        .enforce_equal(&Boolean::TRUE)?;

    Ok(a - b)
}
