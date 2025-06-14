use std::ops::Not;

use ark_crypto_primitives::{
    crh::{
        CRHSchemeGadget,
        poseidon::constraints::{CRHGadget, CRHParametersVar},
    },
    sponge::Absorb,
};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    eq::EqGadget,
    fields::{FieldVar, fp::FpVar},
};
use ark_relations::r1cs::SynthesisError;

use crate::sonobe_backend::circuits::arkworks::step_input::StepInput;

pub trait IVCStateT<F: PrimeField + Absorb> {
    fn new(values: Vec<FpVar<F>>) -> Self;
    fn update(
        self,
        crh_params: &CRHParametersVar<F>,
        step_input: &impl StepInput<F>,
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
        step_input: &impl StepInput<F>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let (source_row, target_row) = step_input.as_two_rows_compressed();

        let new_source_hash_input = [&[self.source_hash], source_row].concat();
        let new_source_hash = CRHGadget::<F>::evaluate(crh_params, &new_source_hash_input)?;
        let new_target_hash_input = [&[self.target_hash], target_row].concat();
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
        step_input: &impl StepInput<F>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let base_updates = self.base.update(crh_params, step_input)?;
        Ok([base_updates, vec![self.info]].concat())
    }
}

#[derive(Clone, Debug)]
pub struct IVCStateConvolution<F: PrimeField, const K: usize> {
    base: IVCState<F>,
    // Should be an array of size K-1, but Rust won't support `K-1` expression, and it would be
    // inconvenient to require from the user to pass here a constant 1 less than kernel size.
    common_row_hashes: Vec<FpVar<F>>,
}

impl<F: PrimeField + Absorb, const K: usize> IVCStateT<F> for IVCStateConvolution<F, K> {
    fn new(values: Vec<FpVar<F>>) -> Self {
        assert_eq!(K % 2, 1, "K must be an odd number");
        assert_eq!(
            values.len(),
            1 + K,
            "IVCStateConvolution requires exactly {} values",
            1 + K
        );
        let common_row_hash = values[2..].to_vec();
        Self {
            base: IVCState::new(values[0..2].to_vec()),
            common_row_hashes: common_row_hash,
        }
    }

    fn update(
        self,
        crh_params: &CRHParametersVar<F>,
        step_input: &impl StepInput<F>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let (new_source_rows, target_row) = step_input.as_row_batch_and_row_compressed::<K>();

        // Compute source and target image hashes as usual. The actual source row is the middle one.
        let reduced_step_input = [new_source_rows[K / 2], target_row].concat();
        let base_updates = self.base.update(crh_params, &reduced_step_input)?;

        // Compute hashes of the new source rows.
        let mut new_source_row_hashes = vec![];
        for row in new_source_rows {
            new_source_row_hashes.push(CRHGadget::<F>::evaluate(crh_params, row)?);
        }

        // Unless the old source row hash is zero (initial state), enforce that the overlapping
        // rows are equal by hash.
        let old_source_row_hashes = self.common_row_hashes;
        for (old, new) in old_source_row_hashes
            .iter()
            .zip(new_source_row_hashes.iter())
        {
            old.conditional_enforce_equal(new, &old.is_zero()?.not())?;
        }

        // Return the updated base and the last K-1 hashes of the source rows - for the integrity
        // check in the next step.
        Ok([&base_updates, &new_source_row_hashes[1..]].concat())
    }
}
