use std::marker::PhantomData;

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
use sonobe::{frontend::FCircuit, Error};

use crate::{VecF, VecFpVar};

#[derive(Clone, Debug)]
pub struct HashStep<F: PrimeField, const WIDTH: usize> {
    poseidon_config: PoseidonConfig<F>,
    _f: PhantomData<F>,
}
impl<F: PrimeField + Absorb, const WIDTH: usize> FCircuit<F> for HashStep<F, WIDTH> {
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
        1 // just the accumulated hash
    }

    fn generate_step_constraints(
        &self,
        cs: ConstraintSystemRef<F>,
        _i: usize,
        z_i: Vec<FpVar<F>>,
        external_inputs: Self::ExternalInputsVar,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        assert_eq!(z_i.len(), self.state_len(), "Incorrect state length");
        let old_hash = z_i[0].clone();

        let crh_params =
            CRHParametersVar::<F>::new_constant(cs.clone(), self.poseidon_config.clone())?;

        let hash_input = [&[old_hash], external_inputs.0.as_slice()].concat();
        let h = CRHGadget::<F>::evaluate(&crh_params, &hash_input)?;

        Ok(vec![h])
    }
}
