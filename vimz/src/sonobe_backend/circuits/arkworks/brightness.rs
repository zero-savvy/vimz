use std::marker::PhantomData;

use ark_bn254::Fr;
use ark_crypto_primitives::{
    crh::{
        poseidon::constraints::{CRHGadget, CRHParametersVar},
        CRHSchemeGadget,
    },
    sponge::{poseidon::PoseidonConfig, Absorb},
};
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use sonobe::{frontend::FCircuit, transcript::poseidon::poseidon_canonical_config, Error};
use sonobe_frontends::utils::{VecF, VecFpVar};

use crate::{
    config::Config, sonobe_backend::circuits::SonobeCircuit, transformation::Transformation,
};

#[derive(Clone, Debug)]
pub struct BrightnessArkworksCircuit<F: PrimeField, const WIDTH: usize> {
    poseidon_config: PoseidonConfig<F>,
    _f: PhantomData<F>,
}

impl<F: PrimeField + Absorb, const WIDTH: usize> FCircuit<F>
    for BrightnessArkworksCircuit<F, WIDTH>
{
    type Params = PoseidonConfig<F>;
    type ExternalInputs = VecF<F, WIDTH>;
    type ExternalInputsVar = VecFpVar<F, WIDTH>;

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
        cs: ConstraintSystemRef<F>,
        _i: usize,
        z_i: Vec<FpVar<F>>,
        external_inputs: Self::ExternalInputsVar,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        assert_eq!(z_i.len(), self.state_len(), "Incorrect state length");
        let old_source_hash = z_i[0].clone();
        let old_target_hash = z_i[1].clone();
        let factor = z_i[2].clone();

        let crh_params =
            CRHParametersVar::<F>::new_constant(cs.clone(), self.poseidon_config.clone())?;

        assert_eq!(
            external_inputs.0.len(),
            Transformation::Brightness.step_input_width(),
            "Incorrect input width"
        );

        let source_row = external_inputs.0[0..WIDTH / 2].to_vec();
        let target_row = external_inputs.0[WIDTH / 2..WIDTH].to_vec();

        let new_source_hash_input = [&[old_source_hash], source_row.as_slice()].concat();
        let new_source_hash = CRHGadget::<F>::evaluate(&crh_params, &new_source_hash_input)?;
        let new_target_hash_input = [&[old_target_hash], target_row.as_slice()].concat();
        let new_target_hash = CRHGadget::<F>::evaluate(&crh_params, &new_target_hash_input)?;

        Ok(vec![new_source_hash, new_target_hash, factor])
    }
}

impl<const WIDTH: usize> SonobeCircuit for BrightnessArkworksCircuit<Fr, WIDTH> {
    fn from_config(_config: &Config) -> Self {
        Self::new(poseidon_canonical_config::<Fr>())
            .expect("Failed to construct HashStep from config")
    }
}
