use std::{fs, path::PathBuf};

use ark_bn254::Fr;
use ark_serialize::{CanonicalDeserialize, Validate};
use rand::{prelude::StdRng, SeedableRng};
use sonobe::{
    folding::nova::PreprocessorParam, transcript::poseidon::poseidon_canonical_config, Decider as _,
    FoldingScheme,
};

use crate::{
    sonobe_backend::{
        circuits::SonobeCircuit,
        decider::{Decider, DeciderParams},
        folding::{Folding, FoldingParams},
    },
    transformation::Transformation,
    COMPRESS_PARAMS,
};

pub struct ParameterProvider {
    lookup_dir: Option<PathBuf>,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
enum ParamType {
    Folding,
    Decider,
}

impl ParamType {
    fn file_extension(&self) -> &'static str {
        match self {
            ParamType::Folding => "folding",
            ParamType::Decider => "decider",
        }
    }
}

impl ParameterProvider {
    pub fn new_on_demand() -> Self {
        Self { lookup_dir: None }
    }

    pub fn new_with_lookup_dir(lookup_dir: PathBuf) -> Self {
        Self {
            lookup_dir: Some(lookup_dir),
        }
    }

    pub fn get_folding_params<Circuit: SonobeCircuit>(
        &self,
        circuit: &Circuit,
        transformation: Transformation,
    ) -> FoldingParams<Circuit>
    where
        FoldingParams<Circuit>: CanonicalDeserialize,
    {
        match self.lookup(transformation, ParamType::Folding) {
            Some(params) => params,
            None => generate_folding_params(circuit),
        }
    }

    pub fn get_decider_params<Circuit: SonobeCircuit>(
        &self,
        folding_params: FoldingParams<Circuit>,
        transformation: Transformation,
    ) -> DeciderParams<Circuit> {
        match self.lookup(transformation, ParamType::Decider) {
            Some(params) => params,
            None => {
                generate_decider_params::<Circuit>(transformation.ivc_state_len(), folding_params)
            }
        }
    }

    fn lookup<Data: CanonicalDeserialize>(
        &self,
        transformation: Transformation,
        param_type: ParamType,
    ) -> Option<Data> {
        let Some(dir) = self.lookup_dir.as_ref() else {
            return None;
        };

        let file_path = dir.join(format!(
            "{transformation:?}.{}",
            param_type.file_extension()
        ));

        let content = fs::read(file_path).ok()?;
        Data::deserialize_with_mode(&*content, COMPRESS_PARAMS, Validate::Yes).ok()
    }
}

pub fn generate_folding_params<Circuit: SonobeCircuit>(
    circuit: &Circuit,
) -> FoldingParams<Circuit> {
    let mut rng = StdRng::from_seed([41; 32]);
    let nova_preprocess_params =
        PreprocessorParam::new(poseidon_canonical_config::<Fr>(), circuit.clone());
    Folding::preprocess(&mut rng, &nova_preprocess_params).expect("Failed to preprocess Nova")
}

pub fn generate_decider_params<Circuit: SonobeCircuit>(
    ivc_state_len: usize,
    folding_params: FoldingParams<Circuit>,
) -> DeciderParams<Circuit> {
    let mut rng = StdRng::from_seed([42; 32]);
    Decider::<Circuit>::preprocess(&mut rng, (folding_params, ivc_state_len))
        .expect("Failed to preprocess decider")
}
