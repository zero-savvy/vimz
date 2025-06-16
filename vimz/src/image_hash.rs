use ark_crypto_primitives::{
    crh::{
        CRHScheme, TwoToOneCRHScheme,
        poseidon::{CRH, TwoToOneCRH},
    },
    sponge::{Absorb, poseidon::PoseidonConfig},
};
use ark_ff::PrimeField;
use image::{ColorType, DynamicImage, GenericImageView};
use sonobe::transcript::poseidon::poseidon_canonical_config;

use crate::PACKING_FACTOR;

pub fn hash_image_arkworks<F: PrimeField + Absorb>(img: &DynamicImage, nrows: Option<usize>) -> F {
    let (_width, height) = img.dimensions();
    let rows = nrows.unwrap_or(height as usize).min(height as usize);

    let crh_params = poseidon_canonical_config::<F>();
    let mut hash = F::zero();

    for row in get_raw_rows(img).iter().take(rows) {
        let packed = pack_pixel_row(row);
        let hashed_row = hash_row::<F>(&crh_params, &packed);
        hash = accumulate_hash(&crh_params, &hash, &hashed_row);
    }

    hash
}

fn get_raw_rows(img: &DynamicImage) -> Vec<Vec<[u8; 3]>> {
    match img.color() {
        ColorType::L8 => img
            .to_luma8()
            .rows()
            .map(|row| row.map(|p| [p.0[0], 0, 0]).collect())
            .collect(),
        ColorType::Rgb8 => img
            .to_rgb8()
            .rows()
            .map(|row| row.map(|p| p.0).collect())
            .collect(),
        _ => panic!("Unsupported image color type: {:?}", img.color()),
    }
}

fn pack_pixel_row<F: PrimeField>(row: &[[u8; 3]]) -> Vec<F> {
    row.chunks(PACKING_FACTOR)
        .map(|chunk| F::from_le_bytes_mod_order(&chunk.concat()))
        .collect()
}

fn hash_row<F: PrimeField + Absorb>(crh_params: &PoseidonConfig<F>, row: &[F]) -> F {
    CRH::evaluate(crh_params, row).expect("Failed to hash row")
}

fn accumulate_hash<F: PrimeField + Absorb>(crh_params: &PoseidonConfig<F>, acc: &F, new: &F) -> F {
    TwoToOneCRH::evaluate(crh_params, acc, new).expect("Failed to accumulate hash")
}
