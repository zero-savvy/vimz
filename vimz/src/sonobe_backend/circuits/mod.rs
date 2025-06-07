use ark_bn254::Fr;
use sonobe::frontend::FCircuit;
use sonobe_frontends::utils::VecF;

use crate::config::Config;

pub mod arkworks;
pub mod circom;

pub trait SonobeCircuit: FCircuit<Fr, ExternalInputs: VecFT> {
    fn from_config(config: &Config) -> Self;
}

/// An auxiliary trait to hide const generics for VecF.
pub trait VecFT {
    fn from_vec(vec: Vec<Fr>) -> Self;
}
impl<const L: usize> VecFT for VecF<Fr, L> {
    fn from_vec(vec: Vec<Fr>) -> Self {
        VecF(vec)
    }
}
