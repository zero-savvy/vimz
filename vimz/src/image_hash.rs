use ark_crypto_primitives::{
    crh::{
        poseidon::{TwoToOneCRH, CRH}, CRHScheme,
        TwoToOneCRHScheme,
    },
    sponge::{poseidon::PoseidonConfig, Absorb},
};
use ark_ff::PrimeField;
use clap::ValueEnum;
use image::{ColorType, DynamicImage};

use crate::{sonobe_backend::circuits::arkworks::poseidon_config, PACKING_FACTOR};

#[derive(Copy, Clone, Debug, ValueEnum)]
pub enum HashMode {
    RowWise,
    BlockWise,
}

pub fn hash_image_arkworks<F: PrimeField + Absorb>(
    img: &DynamicImage,
    mode: HashMode,
    nsteps: Option<usize>,
) -> F {
    let data = match mode {
        HashMode::RowWise => get_raw_rows(img),
        HashMode::BlockWise => get_blocks(img, 40),
    };
    let limit = nsteps.unwrap_or(data.len()).min(data.len());

    let mut hash = F::zero();
    let crh_params = poseidon_config::<F>();
    for chunk in &data[..limit] {
        hash = hash_step(&crh_params, hash, chunk);
    }
    hash
}

fn hash_step<F: PrimeField + Absorb>(
    crh_params: &PoseidonConfig<F>,
    acc: F,
    pixels: &[[u8; 3]],
) -> F {
    let packed = pack_pixels::<F>(pixels);
    let hashed = CRH::evaluate(crh_params, packed.as_slice()).expect("Failed to hash input");
    TwoToOneCRH::evaluate(crh_params, &acc, &hashed).expect("Failed to accumulate hash")
}

fn pack_pixels<F: PrimeField>(pixels: &[[u8; 3]]) -> Vec<F> {
    pixels
        .chunks(PACKING_FACTOR)
        .map(|chunk| F::from_le_bytes_mod_order(&chunk.concat()))
        .collect()
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

fn get_blocks(img: &DynamicImage, block_size: u32) -> Vec<Vec<[u8; 3]>> {
    let rgb_img = img.to_rgb8();
    let (width, height) = rgb_img.dimensions();
    let mut blocks = Vec::new();

    for y in (0..height).step_by(block_size as usize) {
        for x in (0..width).step_by(block_size as usize) {
            let mut block = Vec::new();

            for dy in 0..block_size {
                for dx in 0..block_size {
                    if x + dx < width && y + dy < height {
                        block.push(rgb_img.get_pixel(x + dx, y + dy).0);
                    }
                }
            }

            blocks.push(block);
        }
    }

    blocks
}
