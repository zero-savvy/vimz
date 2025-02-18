use ark_bn254::Fr;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use sonobe::{frontend::FCircuit, utils::PathOrBin, Error};
use sonobe_frontends::{circom::CircomFCircuit, utils::VecF};

pub trait SonobeCircuit: FCircuit<Fr, Params = (PathOrBin, PathOrBin, usize)> {
    fn format_input(input: Vec<Fr>) -> Self::ExternalInputs;
}

#[derive(Clone, Debug)]
pub struct BlurCircuit(CircomFCircuit<Fr, 2>);
impl FCircuit<Fr> for BlurCircuit {
    type Params = <CircomFCircuit<Fr, 2> as FCircuit<Fr>>::Params;
    type ExternalInputs = <CircomFCircuit<Fr, 2> as FCircuit<Fr>>::ExternalInputs;
    type ExternalInputsVar = <CircomFCircuit<Fr, 2> as FCircuit<Fr>>::ExternalInputsVar;

    fn new(params: Self::Params) -> Result<Self, Error> {
        CircomFCircuit::<Fr, 2>::new(params).map(BlurCircuit)
    }

    fn state_len(&self) -> usize {
        self.0.state_len
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

impl SonobeCircuit for BlurCircuit {
    fn format_input(input: Vec<Fr>) -> Self::ExternalInputs {
        VecF(input)
    }
}
