use std::{
    fs,
    fs::{create_dir_all, File},
    io::Write,
    path::{Path, PathBuf},
};

use ark_bn254::Fr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Validate};
use clap::Parser;
use humansize::{format_size, DECIMAL};
use vimz::{
    sonobe_backend::{
        circuits::{arkworks::*, SonobeCircuit},
        decider::DeciderParams,
        folding::FoldingParams,
        parameters::{generate_decider_params, generate_folding_params},
    },
    transformation::{
        Transformation,
        Transformation::{
            Blur, Brightness, Contrast, Crop, Grayscale, Hash, Redact, Resize, Sharpness,
        },
    },
    COMPRESS_PARAMS,
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
        println!("\nProcessing transformation: {t:?}");
        let (folding_params, decider_params) = match t {
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
        save(decider_params, "decider", &cli_config.output_dir, t);
    }
}

fn run<Circuit: SonobeCircuit>(
    circuit: Circuit,
) -> (FoldingParams<Circuit>, DeciderParams<Circuit>) {
    let start = std::time::Instant::now();
    let folding_params = generate_folding_params(&circuit);
    println!("Folding preprocessing took: {:.2?}", start.elapsed());

    let start = std::time::Instant::now();
    let decider_params =
        generate_decider_params::<Circuit>(circuit.state_len(), folding_params.clone());
    println!("Decider preprocessing took: {:.2?}", start.elapsed());

    (folding_params, decider_params)
}

fn save<Data: CanonicalSerialize + CanonicalDeserialize>(
    data: Data,
    data_title: &str,
    output_dir: &Path,
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
        data.serialize_with_mode(&mut serialized, COMPRESS_PARAMS)
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

    let start = std::time::Instant::now();
    let bytes = fs::read(&file_path).expect("Failed to read file");
    let _restored = Data::deserialize_with_mode(&*bytes, COMPRESS_PARAMS, Validate::No)
        .expect("Failed to deserialize data");
    println!(
        "Deserialization {data_title} parameters for {transformation:?} from file should take {:.2?}.",
        start.elapsed()
    );
}
