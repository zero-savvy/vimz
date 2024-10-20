use std::io;

use tracing::level_filters::LevelFilter;
use tracing_subscriber::{fmt::format::FmtSpan, EnvFilter};

fn get_filter() -> EnvFilter {
    EnvFilter::builder()
        .with_default_directive(LevelFilter::WARN.into())
        .from_env_lossy()
        .add_directive("vimz=info".parse().unwrap())
}

pub fn init_logging() {
    tracing_subscriber::fmt()
        .with_writer(io::stdout)
        .with_target(false)
        .with_env_filter(get_filter())
        .with_span_events(FmtSpan::CLOSE)
        .with_level(false)
        .without_time()
        .try_init()
        .expect("Failed to initialize logging");
}
