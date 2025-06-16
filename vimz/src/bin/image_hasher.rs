use std::path::PathBuf;

use ark_bn254::Fr;
use clap::Parser;
use image::{DynamicImage, ImageReader};
use vimz::image_hash::hash_image_arkworks;

#[derive(Parser)]
#[command(
    about = "Image Hasher - a tool for computing Poseidon hash of an image, compatible with the **Sonobe+Arkworks** proving pipeline"
)]
struct Config {
    input_file: PathBuf,
    rows: Option<usize>,
}

fn main() {
    let config = Config::parse();
    let hash = hash_image_arkworks::<Fr>(&read_image(&config.input_file), config.rows);
    println!("{hash}");
}

fn read_image(path: &PathBuf) -> DynamicImage {
    ImageReader::open(path)
        .unwrap_or_else(|e| panic!("Failed to open image file `{}`: {e}", path.display()))
        .decode()
        .expect("Failed to decode image")
}
