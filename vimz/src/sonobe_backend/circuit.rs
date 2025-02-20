use ark_bn254::Fr;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use paste::paste;
use sonobe::{frontend::FCircuit, utils::PathOrBin, Error};
use sonobe_frontends::{circom::CircomFCircuit, utils::VecF};

use crate::transformation::Transformation;

pub trait SonobeCircuit: FCircuit<Fr, Params = (PathOrBin, PathOrBin)> {
    fn format_input(input: Vec<Fr>) -> Self::ExternalInputs;
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
            fn format_input(input: Vec<Fr>) -> Self::ExternalInputs {
                VecF(input)
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
declare_circuit!(Resize);
declare_circuit!(Sharpness);
