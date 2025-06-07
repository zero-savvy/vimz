use ark_bn254::Fr;
use ark_circuits::hash_step::HashStep;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use paste::paste;
use sonobe::{frontend::FCircuit, transcript::poseidon::poseidon_canonical_config, Error};
use sonobe_frontends::circom::CircomFCircuit;

use crate::{config::Config, transformation::Transformation};

pub trait FromVec {
    fn from_vec(vec: Vec<Fr>) -> Self;
}

impl<const L: usize> FromVec for sonobe_frontends::utils::VecF<Fr, L> {
    fn from_vec(vec: Vec<Fr>) -> Self {
        sonobe_frontends::utils::VecF(vec)
    }
}

impl<const L: usize> FromVec for ark_circuits::VecF<Fr, L> {
    fn from_vec(vec: Vec<Fr>) -> Self {
        ark_circuits::VecF(vec)
    }
}

pub trait SonobeCircuit: FCircuit<Fr, ExternalInputs: FromVec> {
    fn from_config(config: &Config) -> Self;
}

impl<const WIDTH: usize> SonobeCircuit for HashStep<Fr, WIDTH> {
    fn from_config(_config: &Config) -> Self {
        Self::new(poseidon_canonical_config::<Fr>())
            .expect("Failed to construct HashStep from config")
    }
}

macro_rules! declare_circuit {
    ($transformation: ident) => {
        declare_circuit!(
            $transformation,
            {Transformation::$transformation.ivc_state_len()},
            {Transformation::$transformation.step_input_width()},
        );
    };
    ($transformation: ident, $sl: expr, $eil: expr $(,)?) => {
        paste! {
        #[derive(Clone, Debug)]
        pub struct [<$transformation Circuit>] (CircomFCircuit<Fr, $sl, $eil>);
        impl FCircuit<Fr> for [<$transformation Circuit>] {
            type Params = <CircomFCircuit<Fr, $sl, $eil> as FCircuit<Fr>>::Params;
            type ExternalInputs = <CircomFCircuit<Fr, $sl, $eil> as FCircuit<Fr>>::ExternalInputs;
            type ExternalInputsVar = <CircomFCircuit<Fr, $sl, $eil> as FCircuit<Fr>>::ExternalInputsVar;

            fn new(params: Self::Params) -> Result<Self, Error> {
                CircomFCircuit::<Fr, $sl, $eil>::new(params).map([<$transformation Circuit>])
            }

            fn state_len(&self) -> usize {
                $sl
            }

            fn generate_step_constraints(
                &self,
                cs: ConstraintSystemRef<Fr>,
                i: usize,
                z_i: Vec<FpVar<Fr>>,
                external_inputs: Self::ExternalInputsVar,
            ) -> Result<Vec<FpVar<Fr>>, SynthesisError> {
                self.0
                    .generate_step_constraints(cs, i, z_i, external_inputs)
            }
        }

        impl SonobeCircuit for [<$transformation Circuit>] {
            fn from_config(config: &Config) -> Self {
                let f_circuit_params = (
                    config.circuit_file().into(),
                    config.witness_generator_file().into(),
                );
                Self::new(f_circuit_params).expect("Failed to create circuit")
            }
        }
        }
    };
}

declare_circuit!(Blur);
declare_circuit!(Brightness);
declare_circuit!(Contrast);
declare_circuit!(Crop);
declare_circuit!(Grayscale);
declare_circuit!(Hash);
declare_circuit!(Redact);
declare_circuit!(Resize);
declare_circuit!(Sharpness);
