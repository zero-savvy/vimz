use clap::Parser;
use config::{Backend, Config};

use crate::logging::init_logging;

const DEMO_STEPS: usize = 5;

mod config;
mod input;
mod logging;
mod nova_snark_backend;
mod sonobe_backend;
mod transformation;

fn main() {
    init_logging();

    let config = Config::parse();
    config.display();

    match config.backend {
        Backend::NovaSnark => nova_snark_backend::run(&config),
        Backend::Sonobe => sonobe_backend::run(&config),
    }
}
