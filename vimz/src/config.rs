use std::{env::current_dir, path::PathBuf};

use clap::{Parser, ValueEnum};
use image::{DynamicImage, ImageReader};

use crate::transformation::{Resolution, Transformation};

/// Supported backends.
#[derive(Copy, Clone, PartialEq, Eq, Debug, ValueEnum)]
pub enum Backend {
    Sonobe,
    NovaSnark,
}

/// Supported circuits frontend for the Sonobe backend.
#[derive(Copy, Clone, Default, PartialEq, Eq, Debug, ValueEnum)]
pub enum Frontend {
    #[default]
    Circom,
    Arkworks,
}

#[derive(Parser)]
#[command(
    version,
    author,
    about = "Prove the truthfulness of your media! \nThe naming rationale: Verifiable Image Manipulation based on ZKP. \nPronunciation: /ˈwɪmzi/, just like whimsy :D",
    long_about = None,
)]
pub struct Config {
    /// The JSON file containing the original and the transformed image data to verify.
    ///
    /// The path is assumed to be relative to the current working directory.
    #[clap(short, long)]
    input: PathBuf,

    ///This file will contain the final Proof to be verified by others.
    ///
    /// The path is assumed to be relative to the current working directory.
    #[clap(short, long)]
    output: Option<PathBuf>,

    /// The R1CS file of the compiled Circom circuit.
    ///
    /// The path is assumed to be relative to the current working directory.
    #[clap(short, long)]
    circuit: PathBuf,

    /// Witness generator file of the circuit.
    ///
    /// The path is assumed to be relative to the current working directory.
    #[clap(short, long)]
    witness_generator: PathBuf,

    /// The transformation function.
    #[clap(short, long, value_enum)]
    pub function: Transformation,

    /// The resolution of the image.
    #[clap(short, long, value_enum)]
    pub resolution: Resolution,

    /// The backend proof system.
    #[clap(short, long, value_enum)]
    pub backend: Backend,

    /// The circuit frontend (applicable only to the Sonobe backend).
    #[clap(long, value_enum, default_value_t = Frontend::default())]
    pub frontend: Frontend,

    /// Run the procedure only on a small part of the image.
    #[clap(short, long)]
    pub demo: bool,

    /// Optional source image for the final IVC verification. Applicable only to the Sonobe + Arkworks pipeline.
    #[clap(long, value_parser = parse_image)]
    pub source_image: Option<DynamicImage>,

    /// Optional target image for the final IVC verification. Applicable only to the Sonobe + Arkworks pipeline.
    #[clap(long, value_parser = parse_image)]
    pub target_image: Option<DynamicImage>,
}

impl Config {
    pub fn new(
        input: PathBuf,
        output: Option<PathBuf>,
        circuit: PathBuf,
        witness_generator: PathBuf,
        function: Transformation,
        resolution: Resolution,
        backend: Backend,
        frontend: Frontend,
        demo: bool,
        source_image: Option<DynamicImage>,
        target_image: Option<DynamicImage>,
    ) -> Self {
        Self {
            input,
            output,
            circuit,
            witness_generator,
            function,
            resolution,
            backend,
            frontend,
            demo,
            source_image,
            target_image,
        }
    }

    fn root_dir() -> PathBuf {
        current_dir().expect("Failed to get the current working directory")
    }

    pub fn input_file(&self) -> PathBuf {
        Self::root_dir().join(&self.input)
    }

    pub fn output_file(&self) -> Option<PathBuf> {
        self.output.as_ref().map(|path| Self::root_dir().join(path))
    }

    pub fn circuit_file(&self) -> PathBuf {
        Self::root_dir().join(&self.circuit)
    }

    pub fn witness_generator_file(&self) -> PathBuf {
        Self::root_dir().join(&self.witness_generator)
    }
}

pub fn parse_image(path: &str) -> Result<DynamicImage, String> {
    ImageReader::open(path)
        .map_err(|e| format!("Failed to open image file `{}`: {e}", path))?
        .decode()
        .map_err(|e| format!("Failed to decode image `{}`: {e}", path))
}

impl Config {
    pub fn display(&self) {
        println!(" ________________________________________________________");
        println!("                                                         ");
        println!(" ██     ██  ██  ███    ███  ████████   Verifiable  Image");
        println!(" ██     ██  ██  ████  ████      ███    Manipulation from");
        println!("  ██   ██   ██  ██ ████ ██     ██      Folded   zkSNARKs");
        println!("   ██ ██    ██  ██  ██  ██   ███                         ");
        println!("    ███     ██  ██      ██  ████████████ v2.0.0 ████████");
        println!(" ________________________________________________________");
        println!("| Selected Backend: {:?}", self.backend);
        if self.backend == Backend::Sonobe {
            println!("| Circuit Frontend: {:?}", self.frontend);
        }
        println!("| Input file: {:?}", self.input);
        println!("| Output file: {:?}", self.output);
        println!("| Selected function: {:?}", self.function);
        println!("| Circuit file: {:?}", self.circuit);
        println!("| Witness generator: {:?}", self.witness_generator);
        println!("| Image resolution: {:?}", self.resolution);
        println!("| Demo mode: {}", self.demo);
        println!(" ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾");
    }
}
