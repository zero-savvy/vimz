use std::{
    marker::PhantomData,
    ops::{Add, Mul, Sub},
};

use ark_bn254::Fr;
use ark_crypto_primitives::{
    crh::poseidon::constraints::CRHParametersVar, sponge::poseidon::PoseidonConfig,
};
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use arkworks_small_values_ops::{abs_diff, enforce_in_binary_bound, enforce_in_bound, min};
use sonobe::{Error, frontend::FCircuit, transcript::poseidon::poseidon_canonical_config};
use sonobe_frontends::utils::{VecF, VecFpVar};

use crate::{
    config::Config,
    sonobe_backend::circuits::{
        SonobeCircuit,
        arkworks::{
            compression::Pixel,
            ivc_state::{IVCStateT, IVCStateWithInfo},
            utils::decompress_row,
        },
    },
    transformation::Transformation,
};

#[derive(Clone, Debug)]
pub struct ContrastArkworksCircuit<F: PrimeField, const WIDTH: usize> {
    poseidon_config: PoseidonConfig<F>,
    _f: PhantomData<F>,
}

impl<const WIDTH: usize> FCircuit<Fr> for ContrastArkworksCircuit<Fr, WIDTH> {
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
        Transformation::Contrast.ivc_state_len()
    }

    fn generate_step_constraints(
        &self,
        cs: ConstraintSystemRef<Fr>,
        _i: usize,
        z_i: Vec<FpVar<Fr>>,
        external_inputs: Self::ExternalInputsVar,
    ) -> Result<Vec<FpVar<Fr>>, SynthesisError> {
        let state = IVCStateWithInfo::new(z_i);

        let factor = state.info();
        enforce_in_binary_bound::<_, 5>(factor)?;

        let source_row = external_inputs.0[0..WIDTH / 2].to_vec();
        let target_row = external_inputs.0[WIDTH / 2..WIDTH].to_vec();

        let source_pixels = decompress_row(cs.clone(), &source_row)?;
        let target_pixels = decompress_row(cs.clone(), &target_row)?;

        let max = FpVar::Constant(Fr::from(2550));
        let precision = FpVar::Constant(Fr::from(10));
        let mean = FpVar::Constant(Fr::from(128));
        let mean_scaled = (&mean).mul(&precision);

        let source = source_pixels.iter().flat_map(Pixel::flatten);

        let target = target_pixels
            .iter()
            .flat_map(Pixel::flatten)
            .map(|p| p.mul(&precision));

        let factor_times_mean = factor.mul(&mean);

        for (source, target) in source.zip(target) {
            // we have to compute (source-128) * factor + 1280 and clamp it to [0, 2550]
            // to avoid underflow issues, we do it in the following steps:
            // 1. compute a = source * factor + 1280
            // 2. compute b = a - factor * 128         clamped to [0, ...)
            // 3. take min(b, 2550)
            let a = source.mul(factor).add(&mean_scaled); // source * factor + 1280
            let to_subtract = min::<_, 14>(cs.clone(), &a, &factor_times_mean)?;
            let b = a.sub(&to_subtract); // a - factor * 128
            let contrasted = min::<_, 13>(cs.clone(), &b, &max)?;

            let diff = abs_diff::<_, 13>(cs.clone(), &contrasted, &target)?;
            enforce_in_bound(&diff, 10)?;
        }

        let crh_params =
            CRHParametersVar::<Fr>::new_constant(cs.clone(), self.poseidon_config.clone())?;
        state.update(&crh_params, &source_row, &target_row)
    }
}

impl<const WIDTH: usize> SonobeCircuit for ContrastArkworksCircuit<Fr, WIDTH> {
    fn from_config(_config: &Config) -> Self {
        Self::new(poseidon_canonical_config::<Fr>())
            .expect("Failed to construct HashStep from config")
    }
}
