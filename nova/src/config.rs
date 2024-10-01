use std::path::PathBuf;

use clap::Parser;

use crate::transformation::{Resolution, Transformation};
use crate::backend::Backend;

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
    pub output: PathBuf,

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
}

impl Config {
    pub fn display(&self) {
        println!(" ________________________________________________________");
        println!("                                                         ");
        println!(" ██     ██  ██  ███    ███  ████████   Verifiable  Image");
        println!(" ██     ██  ██  ████  ████      ███    Manipulation from");
        println!("  ██   ██   ██  ██ ████ ██     ██      Folded   zkSNARKs");
        println!("   ██ ██    ██  ██  ██  ██   ███                         ");
        println!("    ███     ██  ██      ██  ████████████ v1.3.0 ████████");
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
