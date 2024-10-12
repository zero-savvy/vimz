use clap::Parser;
use nova_snark::nova_snark_backend;

use crate::config::{Backend, Config};

mod config;
mod nova_snark;
mod sonobe_backend;
mod time;
mod transformation;

fn main() {
    let config = Config::parse();
    config.display();

    match config.backend {
        Backend::NovaSnark => nova_snark_backend(&config),
        Backend::Sonobe => sonobe_backend::run(&config),
    }
}
