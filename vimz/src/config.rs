use std::{env::current_dir, path::PathBuf};

use clap::{Parser, ValueEnum};

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
    pub input: PathBuf,

    ///This file will contain the final Proof to be verified by others.
    ///
    /// The path is assumed to be relative to the current working directory.
    #[clap(short, long)]
    pub output: Option<PathBuf>,

    /// The R1CS file of the compiled Circom circuit.
    ///
    /// The path is assumed to be relative to the current working directory.
    #[clap(short, long)]
    pub circuit: PathBuf,

    /// Witness generator file of the circuit.
    ///
    /// The path is assumed to be relative to the current working directory.
    #[clap(short, long)]
    pub witness_generator: PathBuf,

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
}

impl Config {
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
