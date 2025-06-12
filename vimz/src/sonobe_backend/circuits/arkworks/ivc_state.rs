use ark_crypto_primitives::{
    crh::{
        CRHSchemeGadget,
        poseidon::constraints::{CRHGadget, CRHParametersVar},
    },
    sponge::Absorb,
};
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::SynthesisError;

pub trait IVCStateT<F: PrimeField + Absorb> {
    fn new(values: Vec<FpVar<F>>) -> Self;
    fn update(
        self,
        crh_params: &CRHParametersVar<F>,
        source_data: &[FpVar<F>],
        target_data: &[FpVar<F>],
    ) -> Result<Vec<FpVar<F>>, SynthesisError>;
}

#[derive(Clone, Debug)]
pub struct IVCState<F: PrimeField> {
    pub source_hash: FpVar<F>,
    pub target_hash: FpVar<F>,
}

impl<F: PrimeField + Absorb> IVCStateT<F> for IVCState<F> {
    fn new(values: Vec<FpVar<F>>) -> Self {
        assert_eq!(values.len(), 2, "IVCState requires exactly 2 values");
        Self {
            source_hash: values[0].clone(),
            target_hash: values[1].clone(),
        }
    }

    fn update(
        self,
        crh_params: &CRHParametersVar<F>,
        source_data: &[FpVar<F>],
        target_data: &[FpVar<F>],
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let new_source_hash_input = [&[self.source_hash], source_data].concat();
        let new_source_hash = CRHGadget::<F>::evaluate(crh_params, &new_source_hash_input)?;
        let new_target_hash_input = [&[self.target_hash], target_data].concat();
        let new_target_hash = CRHGadget::<F>::evaluate(crh_params, &new_target_hash_input)?;

        Ok(vec![new_source_hash, new_target_hash])
    }
}

#[derive(Clone, Debug)]
pub struct IVCStateWithInfo<F: PrimeField> {
    base: IVCState<F>,
    info: FpVar<F>,
}

impl<F: PrimeField> IVCStateWithInfo<F> {
    pub fn info(&self) -> &FpVar<F> {
        &self.info
    }
}

impl<F: PrimeField + Absorb> IVCStateT<F> for IVCStateWithInfo<F> {
    fn new(values: Vec<FpVar<F>>) -> Self {
        assert_eq!(values.len(), 3, "IVCState requires exactly 3 values");
        Self {
            base: IVCState::new(values[0..2].to_vec()),
            info: values[2].clone(),
        }
    }

    fn update(
        self,
        crh_params: &CRHParametersVar<F>,
        source_data: &[FpVar<F>],
        target_data: &[FpVar<F>],
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let base_updates = self.base.update(crh_params, source_data, target_data)?;
        Ok([base_updates, vec![self.info]].concat())
    }
}
