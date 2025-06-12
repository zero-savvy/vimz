use std::marker::PhantomData;

use ark_bn254::Fr;
use ark_crypto_primitives::{
    crh::poseidon::constraints::CRHParametersVar, sponge::poseidon::PoseidonConfig,
};
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget, fields::fp::FpVar};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use arkworks_small_values_ops::{abs_diff, min};
use sonobe::{frontend::FCircuit, transcript::poseidon::poseidon_canonical_config, Error};
use sonobe_frontends::utils::{VecF, VecFpVar};

use crate::{
    config::Config,
    sonobe_backend::circuits::{
        arkworks::{
            compression::{decompress_gray_row, decompress_row},
            ivc_state::{IVCState, IVCStateT},
        },
        SonobeCircuit,
    },
    transformation::Transformation,
};

#[derive(Clone, Debug)]
pub struct GrayscaleArkworksCircuit<F: PrimeField, const WIDTH: usize> {
    poseidon_config: PoseidonConfig<F>,
    _f: PhantomData<F>,
}

impl<const WIDTH: usize> FCircuit<Fr> for GrayscaleArkworksCircuit<Fr, WIDTH> {
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
        Transformation::Grayscale.ivc_state_len()
    }

    fn generate_step_constraints(
        &self,
        cs: ConstraintSystemRef<Fr>,
        _i: usize,
        z_i: Vec<FpVar<Fr>>,
        external_inputs: Self::ExternalInputsVar,
    ) -> Result<Vec<FpVar<Fr>>, SynthesisError> {
        let state = IVCState::new(z_i);

        let source_row = external_inputs.0[0..WIDTH / 2].to_vec();
        let target_row = external_inputs.0[WIDTH / 2..WIDTH].to_vec();

        let source_pixels = decompress_row(cs.clone(), &source_row)?;
        let target_pixels = decompress_gray_row(cs.clone(), &target_row)?;

        let r_scale = FpVar::Constant(Fr::from(299));
        let g_scale = FpVar::Constant(Fr::from(587));
        let b_scale = FpVar::Constant(Fr::from(114));
        let full_scale = FpVar::Constant(Fr::from(1000));

        for (source, target) in source_pixels.iter().zip(target_pixels.iter()) {
            let gray = &r_scale * &source.r + &g_scale * &source.g + &b_scale * &source.b;
            let diff = abs_diff::<_, 18>(cs.clone(), &gray, &(target * &full_scale))?;

            // ensure the difference is less than full_scale
            let min_with_scale = min::<_, 18>(cs.clone(), &diff, &full_scale)?;
            min_with_scale.enforce_equal(&diff)?
        }

        let crh_params =
            CRHParametersVar::<Fr>::new_constant(cs.clone(), self.poseidon_config.clone())?;
        state.update(&crh_params, &source_row, &target_row)
    }
}

impl<const WIDTH: usize> SonobeCircuit for GrayscaleArkworksCircuit<Fr, WIDTH> {
    fn from_config(_config: &Config) -> Self {
        Self::new(poseidon_canonical_config::<Fr>())
            .expect("Failed to construct HashStep from config")
    }
}
