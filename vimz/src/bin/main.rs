use clap::Parser;
use vimz::{
    config::{Backend, Config},
    logging::init_logging,
    nova_snark_backend, sonobe_backend,
};

fn main() {
    init_logging();

    let config = Config::parse();
    config.display();

    match config.backend {
        Backend::NovaSnark => nova_snark_backend::run(&config),
        Backend::Sonobe => sonobe_backend::run(&config),
    }
}
