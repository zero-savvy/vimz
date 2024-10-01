use clap::ValueEnum;

/// Supported backends.
#[derive(Copy, Clone, PartialEq, Eq, Debug, ValueEnum)]
pub enum Backend {
    Sonobe,
    NovaSnark
}