use std::path::PathBuf;

use ark_bn254::Fr;
use ark_crypto_primitives::{
    crh::{
        poseidon::{TwoToOneCRH, CRH}, CRHScheme,
        TwoToOneCRHScheme,
    },
    sponge::{poseidon::PoseidonConfig, Absorb},
};
use ark_ff::PrimeField;
use clap::Parser;
use image::{DynamicImage, GenericImageView, ImageReader};
use num_traits::Zero;
use sonobe::transcript::poseidon::poseidon_canonical_config;

#[derive(Parser)]
#[command(
    about = "Image Hasher - a tool for computing Poseidon hash of an image, compatible with the **Sonobe+Arkworks** proving pipeline"
)]
struct Config {
    input_file: PathBuf,
    rows: Option<usize>,
}

const PACKING_FACTOR: usize = 10;

fn main() {
    let config = Config::parse();
    let rgb_image = read_image(&config.input_file).to_rgb8();

    let (_width, height) = rgb_image.dimensions();
    let rows = config.rows.unwrap_or(height as usize).min(height as usize);

    let crh_params = poseidon_canonical_config::<Fr>();
    let mut hash = Fr::zero();

    for row in rgb_image.rows().take(rows) {
        let raw_row = row.map(|p| p.0).collect();
        let packed = pack_pixel_row::<Fr, 3>(&raw_row);
        let hashed_row = hash_row::<Fr>(&crh_params, &packed);
        hash = accumulate_hash(&crh_params, &hash, &hashed_row);
    }

    println!("Computed hash: {hash}");
}

fn read_image(path: &PathBuf) -> DynamicImage {
    ImageReader::open(path)
        .unwrap_or_else(|e| panic!("Failed to open image file `{}`: {e}", path.display()))
        .decode()
        .expect("Failed to decode image")
}

fn pack_pixel_row<F: PrimeField, const CHANNELS: usize>(row: &Vec<[u8; CHANNELS]>) -> Vec<F> {
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
