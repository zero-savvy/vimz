use std::{
    marker::PhantomData,
    ops::{Mul, MulAssign},
};

use ark_bn254::Fr;
use ark_crypto_primitives::{
    crh::{
        poseidon::constraints::{CRHGadget, CRHParametersVar},
        CRHSchemeGadget,
    },
    sponge::poseidon::PoseidonConfig,
};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::AllocVar,
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    R1CSVar,
};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use num_traits::{One, Zero};
use sonobe::{frontend::FCircuit, transcript::poseidon::poseidon_canonical_config, Error};
use sonobe_frontends::utils::{VecF, VecFpVar};

use crate::{
    config::Config,
    sonobe_backend::circuits::{
        arkworks::{
            compression::Pixel,
            utils::{cap, decompress_row},
        },
        SonobeCircuit,
    },
    transformation::Transformation,
};

#[derive(Clone, Debug)]
pub struct BrightnessArkworksCircuit<F: PrimeField, const WIDTH: usize> {
    poseidon_config: PoseidonConfig<F>,
    _f: PhantomData<F>,
}

impl<const WIDTH: usize> FCircuit<Fr> for BrightnessArkworksCircuit<Fr, WIDTH> {
    type Params = PoseidonConfig<Fr>;
    type ExternalInputs = VecF<Fr, WIDTH>;
    type ExternalInputsVar = VecFpVar<Fr, WIDTH>;

    fn new(poseidon_config: Self::Params) -> Result<Self, Error> {
        Ok(Self {
            poseidon_config,
            _f: PhantomData,
        })
    }

    fn state_len(&self) -> usize {
        Transformation::Brightness.ivc_state_len()
    }

    fn generate_step_constraints(
        &self,
        cs: ConstraintSystemRef<Fr>,
        _i: usize,
        z_i: Vec<FpVar<Fr>>,
        external_inputs: Self::ExternalInputsVar,
    ) -> Result<Vec<FpVar<Fr>>, SynthesisError> {
        assert_eq!(z_i.len(), self.state_len(), "Incorrect state length");
        let old_source_hash = z_i[0].clone();
        let old_target_hash = z_i[1].clone();
        let factor = z_i[2].clone();

        let mut x = FpVar::Constant(1.into());
        for i in 0..32 {
            x.mul_assign(factor.clone() - FpVar::Constant(Fr::from(i as u64)));
        }
        x.is_zero()?.enforce_equal(&Boolean::TRUE)?;

        let crh_params =
            CRHParametersVar::<Fr>::new_constant(cs.clone(), self.poseidon_config.clone())?;

        assert_eq!(
            external_inputs.0.len(),
            Transformation::Brightness.step_input_width(),
            "Incorrect input width"
        );

        let source_row = external_inputs.0[0..WIDTH / 2].to_vec();
        let target_row = external_inputs.0[WIDTH / 2..WIDTH].to_vec();

        let new_source_hash_input = [&[old_source_hash], source_row.as_slice()].concat();
        let new_source_hash = CRHGadget::<Fr>::evaluate(&crh_params, &new_source_hash_input)?;
        let new_target_hash_input = [&[old_target_hash], target_row.as_slice()].concat();
        let new_target_hash = CRHGadget::<Fr>::evaluate(&crh_params, &new_target_hash_input)?;

        let source_pixels = decompress_row(cs.clone(), &source_row)?;
        let target_pixels = decompress_row(cs.clone(), &target_row)?;

        let max = FpVar::new_constant(cs.clone(), Fr::from(2550))?;
        let precision = FpVar::new_constant(cs.clone(), Fr::from(10))?;

        let source_scaled = source_pixels
            .iter()
            .flat_map(Pixel::flatten)
            .map(|p| p.mul(&factor));

        let target_with_precision = target_pixels
            .iter()
            .flat_map(Pixel::flatten)
            .map(|p| p.mul(&precision));

        for (source, target) in source_scaled.zip(target_with_precision) {
            let source = cap(cs.clone(), &source, &max)?;

            let u = FpVar::new_witness(cs.clone(), || {
                let sv = source.value()?;
                let tv = target.value()?;
                if sv < tv {
                    Ok(tv - sv)
                } else {
                    Ok(Fr::zero())
                }
            })?;

            let v = FpVar::new_witness(cs.clone(), || {
                let sv = source.value()?;
                let tv = target.value()?;
                if sv > tv {
                    Ok(sv - tv)
                } else {
                    Ok(Fr::zero())
                }
            })?;

            u.clone().mul(&v).is_zero()?.enforce_equal(&Boolean::TRUE)?;
            (source.clone() + u.clone() - v.clone() - target.clone())
                .is_zero()?
                .enforce_equal(&Boolean::TRUE)?;

            let mut u_range = FpVar::Constant(Fr::one());
            let mut v_range = FpVar::Constant(Fr::one());
            
            for i in 0..=10 {
                u_range *= u.clone() - Fr::from(i as u64);
                v_range *= v.clone() - Fr::from(i as u64);
            }
            u_range.is_zero()?.enforce_equal(&Boolean::TRUE)?;
            v_range.is_zero()?.enforce_equal(&Boolean::TRUE)?;
        }

        Ok(vec![new_source_hash, new_target_hash, factor])
    }
}

impl<const WIDTH: usize> SonobeCircuit for BrightnessArkworksCircuit<Fr, WIDTH> {
    fn from_config(_config: &Config) -> Self {
        Self::new(poseidon_canonical_config::<Fr>())
            .expect("Failed to construct HashStep from config")
    }
}
