use clap::Parser;
use config::{Backend, Config};

mod config;
mod input;
mod nova_snark_backend;
mod sonobe_backend;
mod time;
mod transformation;

fn main() {
    let config = Config::parse();
    config.display();

    match config.backend {
        Backend::NovaSnark => nova_snark_backend::run(&config),
        Backend::Sonobe => sonobe_backend::run(&config),
    }
}
