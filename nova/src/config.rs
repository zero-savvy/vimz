use std::{env::current_dir, path::PathBuf};

use clap::{Parser, ValueEnum};

use crate::transformation::{Resolution, Transformation};

/// Supported backends.
#[derive(Copy, Clone, PartialEq, Eq, Debug, ValueEnum)]
pub enum Backend {
    Sonobe,
    NovaSnark,
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
    output: PathBuf,

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
}

impl Config {
    fn root_dir() -> PathBuf {
        current_dir().expect("Failed to get the current working directory")
    }

    pub fn input_file(&self) -> PathBuf {
        Self::root_dir().join(&self.input)
    }

    pub fn output_file(&self) -> PathBuf {
        Self::root_dir().join(&self.output)
    }

    pub fn circuit_file(&self) -> PathBuf {
        Self::root_dir().join(&self.circuit)
    }

    pub fn witness_generator_file(&self) -> PathBuf {
        Self::root_dir().join(&self.witness_generator)
    }
}

impl Config {
    pub fn display(&self) {
        println!(" ________________________________________________________");
        println!("                                                         ");
        println!(" ██     ██  ██  ███    ███  ████████   Verifiable  Image");
        println!(" ██     ██  ██  ████  ████      ███    Manipulation from");
        println!("  ██   ██   ██  ██ ████ ██     ██      Folded   zkSNARKs");
        println!("   ██ ██    ██  ██  ██  ██   ███                         ");
        println!("    ███     ██  ██      ██  ████████████ v1.4.0 ████████");
        println!(" ________________________________________________________");
        println!("| Selected Backend: {:?}", self.backend);
        println!("| Input file: {:?}", self.input);
        println!("| Output file: {:?}", self.output);
        println!("| Selected function: {:?}", self.function);
        println!("| Circuit file: {:?}", self.circuit);
        println!("| Witness generator: {:?}", self.witness_generator);
        println!("| Image resolution: {:?}", self.resolution);
        println!(" ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾");
    }
}
