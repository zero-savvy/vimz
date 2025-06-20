use ark_bn254::Fr;
use clap::Parser;
use image::DynamicImage;
use vimz::{
    config::parse_image,
    image_hash::{HashMode, hash_image_arkworks},
};

#[derive(Parser)]
#[command(
    about = "Image Hasher - a tool for computing Poseidon hash of an image, compatible with the **Sonobe+Arkworks** proving pipeline"
)]
struct Config {
    #[clap(value_parser = parse_image)]
    img: DynamicImage,
    rows: Option<usize>,
    #[clap(default_value = "row-wise")]
    mode: HashMode,
}

fn main() {
    let config = Config::parse();
    let hash = hash_image_arkworks::<Fr>(&config.img, config.mode, config.rows);
    println!("{hash}");
}
