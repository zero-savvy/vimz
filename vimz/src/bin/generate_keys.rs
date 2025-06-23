use std::{
    fs::{create_dir_all, File},
    io::Write,
    path::PathBuf,
};

use ark_bn254::Fr;
use ark_serialize::CanonicalSerialize;
use clap::Parser;
use humansize::{format_size, DECIMAL};
use rand::{prelude::StdRng, SeedableRng};
use sonobe::{
    folding::nova::PreprocessorParam, transcript::poseidon::poseidon_canonical_config,
    FoldingScheme,
};
use vimz::{
    sonobe_backend::{
        circuits::{arkworks::*, SonobeCircuit},
        folding::{Folding, FoldingParams},
    },
    transformation::{
        Transformation,
        Transformation::{
            Blur, Brightness, Contrast, Crop, Grayscale, Hash, Redact, Resize, Sharpness,
        },
    },
    COMPRESS_KEYS,
};

const ALL_TRANSFORMATIONS: [Transformation; 9] = [
    Blur, Brightness, Contrast, Crop, Grayscale, Hash, Redact, Resize, Sharpness,
];

#[derive(Parser)]
#[clap(
    about = "Preprocess VIMz circuits for Sonobe+Arkworks pipeline and save generated keys to disk for later use."
)]
struct CLIConfig {
    /// Image transformation for which to generate keys. If none, keys for all transformations will be generated.
    #[clap(long)]
    transformation: Option<Transformation>,
    /// Path to the output directory where keys will be saved.
    #[clap(long, default_value = "../keys/")]
    output_dir: PathBuf,
}

fn main() {
    let cli_config = CLIConfig::parse();
    let transformations = match cli_config.transformation {
        Some(transformation) => vec![transformation],
        None => ALL_TRANSFORMATIONS.to_vec(),
    };

    for t in transformations {
        let folding_params = match t {
            Blur => run(BlurArkworksCircuit::<Fr>::with_default_poseidon_config()),
            Brightness => run(BrightnessArkworksCircuit::<Fr>::with_default_poseidon_config()),
            Contrast => run(ContrastArkworksCircuit::<Fr>::with_default_poseidon_config()),
            Crop => run(CropArkworksCircuit::<Fr>::with_default_poseidon_config()),
            Grayscale => run(GrayscaleArkworksCircuit::<Fr>::with_default_poseidon_config()),
            Hash => run(HashArkworksCircuit::<Fr>::with_default_poseidon_config()),
            Redact => run(RedactArkworksCircuit::<Fr>::with_default_poseidon_config()),
            Resize => run(ResizeArkworksCircuit::<Fr>::with_default_poseidon_config()),
            Sharpness => run(SharpnessArkworksCircuit::<Fr>::with_default_poseidon_config()),
        };
        save(folding_params, "folding", &cli_config.output_dir, t);
    }
}

fn run<Circuit: SonobeCircuit>(circuit: Circuit) -> FoldingParams<Circuit> {
    let mut rng = StdRng::from_seed([41; 32]);

    let start = std::time::Instant::now();

    let nova_preprocess_params =
        PreprocessorParam::new(poseidon_canonical_config::<Fr>(), circuit.clone());
    let nova_params =
        Folding::preprocess(&mut rng, &nova_preprocess_params).expect("Failed to preprocess Nova");

    println!("Folding preprocessing took: {:.2?}", start.elapsed());

    nova_params
}

fn save<Data: CanonicalSerialize>(
    data: Data,
    data_title: &str,
    output_dir: &PathBuf,
    transformation: Transformation,
) {
    let file_path = output_dir.join(format!("{transformation:?}.{data_title}"));
    if let Some(parent) = file_path.parent() {
        create_dir_all(parent).expect("Failed to create output directory");
    }
    let mut file = File::create(&file_path).expect("Failed to create output file");

    let start = std::time::Instant::now();
    let size = {
        let mut serialized = vec![];
        data.serialize_with_mode(&mut serialized, COMPRESS_KEYS)
            .expect("Failed to serialize data");

        file.write_all(serialized.as_slice())
            .expect("Failed to write data to file");
        serialized.len()
    };

    println!(
        "Parameters for {transformation:?} {data_title} saved to {file_path:?}. Took {:.2?}. Size: {}.",
        start.elapsed(),
        format_size(size, DECIMAL)
    );
}
