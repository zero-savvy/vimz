use ark_crypto_primitives::{
    crh::{
        CRHScheme, TwoToOneCRHScheme,
        poseidon::{CRH, TwoToOneCRH},
    },
    sponge::{Absorb, poseidon::PoseidonConfig},
};
use ark_ff::PrimeField;
use image::DynamicImage;
use sonobe::transcript::poseidon::poseidon_canonical_config;

const PACKING_FACTOR: usize = 10;

pub fn hash_image_arkworks<F: PrimeField + Absorb>(img: &DynamicImage, nrows: Option<usize>) -> F {
    let rgb_image = img.to_rgb8();

    let (_width, height) = rgb_image.dimensions();
    let rows = nrows.unwrap_or(height as usize).min(height as usize);

    let crh_params = poseidon_canonical_config::<F>();
    let mut hash = F::zero();

    for row in rgb_image.rows().take(rows) {
        let raw_row = row.map(|p| p.0).collect::<Vec<_>>();
        let packed = pack_pixel_row::<F, 3>(&raw_row);
        let hashed_row = hash_row::<F>(&crh_params, &packed);
        hash = accumulate_hash(&crh_params, &hash, &hashed_row);
    }

    hash
}

fn pack_pixel_row<F: PrimeField, const CHANNELS: usize>(row: &[[u8; CHANNELS]]) -> Vec<F> {
    let mut packed = Vec::new();
    for chunk in row.chunks(PACKING_FACTOR) {
        let mut bytes = vec![];
        for &pixel in chunk {
            match CHANNELS {
                1 => {
                    bytes.extend([pixel[0], 0, 0]);
                }
                3 => {
                    bytes.extend(pixel);
                }
                _ => unreachable!("Unexpected pixel length: {}", pixel.len()),
            }
        }
        packed.push(F::from_le_bytes_mod_order(&bytes));
    }
    packed
}

fn hash_row<F: PrimeField + Absorb>(crh_params: &PoseidonConfig<F>, row: &[F]) -> F {
    CRH::evaluate(crh_params, row).expect("Failed to hash row")
}

fn accumulate_hash<F: PrimeField + Absorb>(crh_params: &PoseidonConfig<F>, acc: &F, new: &F) -> F {
    TwoToOneCRH::evaluate(crh_params, acc, new).expect("Failed to accumulate hash")
}
