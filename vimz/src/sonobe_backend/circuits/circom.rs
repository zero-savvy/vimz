use ark_bn254::Fr;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use paste::paste;
use sonobe::{frontend::FCircuit, Error};
use sonobe_frontends::circom::CircomFCircuit;

use super::SonobeCircuit;
use crate::{config::Config, transformation::Transformation};

macro_rules! declare_circom_circuit {
    ($transformation: ident) => {
        declare_circom_circuit!(
            $transformation,
            {Transformation::$transformation.ivc_state_len()},
            {Transformation::$transformation.step_input_width()},
        );
    };
    ($transformation: ident, $sl: expr, $eil: expr $(,)?) => {
        paste! {
        #[derive(Clone, Debug)]
        pub struct [<$transformation CircomCircuit>] (CircomFCircuit<Fr, $sl, $eil>);
        impl FCircuit<Fr> for [<$transformation CircomCircuit>] {
            type Params = <CircomFCircuit<Fr, $sl, $eil> as FCircuit<Fr>>::Params;
            type ExternalInputs = <CircomFCircuit<Fr, $sl, $eil> as FCircuit<Fr>>::ExternalInputs;
            type ExternalInputsVar = <CircomFCircuit<Fr, $sl, $eil> as FCircuit<Fr>>::ExternalInputsVar;

            fn new(params: Self::Params) -> Result<Self, Error> {
                CircomFCircuit::<Fr, $sl, $eil>::new(params).map([<$transformation CircomCircuit>])
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

        impl SonobeCircuit for [<$transformation CircomCircuit>] {
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

declare_circom_circuit!(Blur);
declare_circom_circuit!(Brightness);
declare_circom_circuit!(Contrast);
declare_circom_circuit!(Crop);
declare_circom_circuit!(Grayscale);
declare_circom_circuit!(Hash);
declare_circom_circuit!(Redact);
declare_circom_circuit!(Resize);
declare_circom_circuit!(Sharpness);
