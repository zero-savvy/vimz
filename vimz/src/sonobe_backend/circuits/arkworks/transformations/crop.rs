use ark_crypto_primitives::{
    crh::{
        CRHSchemeGadget,
        poseidon::constraints::{CRHGadget, CRHParametersVar},
    },
    sponge::Absorb,
};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{
    R1CSVar,
    alloc::AllocVar,
    boolean::Boolean,
    eq::EqGadget,
    fields::{FieldVar, fp::FpVar},
};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use arkworks_small_values_ops::{le, one_hot_encode};

use crate::{
    PACKING_FACTOR, circuit_from_step_function,
    sonobe_backend::circuits::arkworks::{
        compression::pack,
        ivc_state::{IVCStateT, IVCStateWithInfo},
        step_input::StepInput,
    },
    transformation::Transformation,
};

const CROP_WIDTH: usize = 640;
const CROP_HEIGHT: usize = 480;

fn generate_step_constraints<F: PrimeField + Absorb>(
    cs: ConstraintSystemRef<F>,
    z_i: Vec<FpVar<F>>,
    external_inputs: Vec<FpVar<F>>,
    crh_params: CRHParametersVar<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let state = IVCStateWithInfo::new(z_i);
    let info = Info::decode(cs.clone(), state.info())?;

    let row_unpacked = external_inputs.as_single_row_unpacked(cs.clone())?;
    let subrow_unpacked = get_subrow(cs.clone(), &row_unpacked, &info.crop_col)?;

    let within_crop_area =
        check_if_within_crop_area(cs.clone(), &info.current_row, &info.crop_row)?;

    update_state(
        state,
        &row_unpacked,
        &subrow_unpacked,
        within_crop_area,
        info,
        &crh_params,
    )
}

circuit_from_step_function!(Crop, generate_step_constraints);

struct Info<F: PrimeField> {
    current_row: FpVar<F>,
    crop_row: FpVar<F>,
    crop_col: FpVar<F>,
}

impl<F: PrimeField> Info<F> {
    pub fn decode(cs: ConstraintSystemRef<F>, encoded: &FpVar<F>) -> Result<Self, SynthesisError> {
        // 1) Convert the encoded value into bits.
        let bits = encoded
            .value()
            .map(|raw_value| raw_value.into_bigint().to_bits_le());
        let f_from_bits =
            |i| Ok(F::from_bigint(<F::BigInt>::from_bits_le(&bits.clone()?[i..i + 12])).unwrap());

        // 2) Compute the decoded witness values.
        let newborn = Info {
            current_row: FpVar::new_witness(cs.clone(), || f_from_bits(0))?,
            crop_row: FpVar::new_witness(cs.clone(), || f_from_bits(12))?,
            crop_col: FpVar::new_witness(cs.clone(), || f_from_bits(24))?,
        };

        // 3) Ensure integrity
        newborn.encode().enforce_equal(encoded)?;

        // 4) Return the info struct.
        Ok(newborn)
    }

    pub fn bump_current_row(&mut self) {
        self.current_row += FpVar::Constant(F::one());
    }

    pub fn encode(&self) -> FpVar<F> {
        self.crop_col.clone() * FpVar::Constant(F::from(2).pow([24]))
            + self.crop_row.clone() * FpVar::Constant(F::from(2).pow([12]))
            + self.current_row.clone()
    }
}

fn get_subrow<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    row: &[FpVar<F>],
    crop_index: &FpVar<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    // 1) Convert index to one-hot encoding.
    let crop_start_one_hot = one_hot_encode::<_, 1280>(cs.clone(), crop_index)?;

    // 2) Create a matrix that represents the crop area, by shifting the one-hot encoding CROP_WIDTH times.
    let mut matrix = vec![];
    for i in 0..CROP_WIDTH {
        let mut row = vec![];
        for _ in 0..i {
            row.push(FpVar::zero());
        }
        for indicator in &crop_start_one_hot {
            row.push(indicator.clone());
        }
        matrix.push(row);
    }

    // 3) Multiply the row by the matrix to get the subrow.
    matrix_vector_product(&matrix, row)
}

fn matrix_vector_product<F: PrimeField>(
    matrix: &[Vec<FpVar<F>>],
    vector: &[FpVar<F>],
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let mut result = vec![];
    for row in matrix {
        let mut sum = FpVar::zero();
        for (i, entry) in row.iter().enumerate() {
            sum += entry * &vector[i];
        }
        result.push(sum);
    }
    Ok(result)
}

fn check_if_within_crop_area<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    current_row: &FpVar<F>,
    crop_row: &FpVar<F>,
) -> Result<Boolean<F>, SynthesisError> {
    // BIT BOUND: both `current_row` and `crop_row` are 12 bits
    let after_start = le::<_, 12>(cs.clone(), crop_row, current_row)?;

    let crop_end = crop_row + FpVar::Constant(F::from((CROP_HEIGHT - 1) as u128));
    // BIT BOUND: `current_row` is 12 bits, `crop_end` must not exceed `current_row`, thus it is also 12 bits
    let before_end = le::<_, 12>(cs.clone(), current_row, &crop_end)?;

    match (after_start, before_end) {
        // We have to go down to `AllocatedBool` to perform the AND operation.
        (Boolean::Var(after_start), Boolean::Var(before_end)) => {
            Ok(Boolean::from(after_start.and(&before_end)?))
        }
        _ => unreachable!("Area indicators are not constants"),
    }
}

fn update_state<F: PrimeField + Absorb>(
    old_state: IVCStateWithInfo<F>,
    row_unpacked: &[FpVar<F>],
    subrow_unpacked: &[FpVar<F>],
    within_crop_area: Boolean<F>,
    mut info: Info<F>,
    crh_params: &CRHParametersVar<F>,
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    // 1) Pack rows - in the IVC state we hash the packed rows.
    let pack_row = |r: &[FpVar<F>]| {
        r.chunks(PACKING_FACTOR)
            .map(|chunk| pack(chunk))
            .collect::<Vec<_>>()
    };
    let row_packed = pack_row(row_unpacked);
    let subrow_packed = pack_row(subrow_unpacked);

    // 2) Update the source hash
    let new_source_hash = CRHGadget::<F>::evaluate(
        crh_params,
        &[&[old_state.base.source_hash], row_packed.as_slice()].concat(),
    )?;

    // 3) If we are within the crop area, update the target hash.
    let new_target_hash = within_crop_area.select(
        &CRHGadget::<F>::evaluate(
            crh_params,
            &[
                &[old_state.base.target_hash.clone()],
                subrow_packed.as_slice(),
            ]
            .concat(),
        )?,
        &old_state.base.target_hash,
    )?;

    // 4) Update the current row in the info.
    info.bump_current_row();

    Ok(vec![new_source_hash, new_target_hash, info.encode()])
}
