use tracing::level_filters::LevelFilter;
use tracing_subscriber::{
    fmt,
    fmt::format::{FmtSpan, Format},
    layer::SubscriberExt,
    util::SubscriberInitExt,
    EnvFilter,
};

pub fn init_logging() {
    let format = Format::default().without_time().with_target(false);

    let layer = fmt::layer()
        .with_span_events(FmtSpan::CLOSE)
        .with_ansi(true)
        .event_format(format);

    tracing_subscriber::registry()
        .with(layer)
        .with(get_filter())
        .init();
}

fn get_filter() -> EnvFilter {
    EnvFilter::builder()
        .with_default_directive(LevelFilter::WARN.into())
        .from_env_lossy()
        .add_directive("vimz=info".parse().unwrap())
}
