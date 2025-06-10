use std::fmt::Debug;

use tracing::{
    field::{Field, Visit},
    level_filters::LevelFilter,
};
use tracing_subscriber::{
    EnvFilter,
    field::RecordFields,
    fmt,
    fmt::{
        FormatFields,
        format::{DefaultFields, FmtSpan, Format, Writer},
    },
    layer::SubscriberExt,
    util::SubscriberInitExt,
};

/// Set up and initialize logging for the application.
pub fn init_logging() {
    let format = Format::default().without_time().with_target(false);

    let layer = fmt::layer()
        .with_span_events(FmtSpan::CLOSE)
        .with_ansi(true)
        .event_format(format)
        .fmt_fields(VIMzFieldFormatter);

    tracing_subscriber::registry()
        .with(layer)
        .with(get_filter())
        .init();
}

/// Get the filter for the logger. This will set the default log level to WARN, but will allow
/// the user to override this with the `RUST_LOG` environment variable. Additionally, it will
/// set the log level for the `vimz` module to INFO.
fn get_filter() -> EnvFilter {
    EnvFilter::builder()
        .with_default_directive(LevelFilter::WARN.into())
        .from_env_lossy()
        .add_directive("vimz=info".parse().unwrap())
}

/// Custom field formatter for VIMz. Essentially, this behaves like the default field formatter,
/// but it will report span time in a nicer format.
struct VIMzFieldFormatter;
impl<'writer> FormatFields<'writer> for VIMzFieldFormatter {
    fn format_fields<R: RecordFields>(
        &self,
        writer: Writer<'writer>,
        fields: R,
    ) -> std::fmt::Result {
        let mut visitor = VIMzFieldVisitor::default();
        fields.record(&mut visitor);
        visitor.dump(writer, fields)
    }
}

#[derive(Default)]
struct VIMzFieldVisitor {
    span_closing_time: Option<String>,
}

impl VIMzFieldVisitor {
    /// Format `fields`. If it happens that it is representing a span closing, then we will format
    /// the time in a nicer format. Otherwise, we will use the default field formatter.
    fn dump<R: RecordFields>(self, mut writer: Writer, fields: R) -> std::fmt::Result {
        match self.span_closing_time {
            None => DefaultFields::new().format_fields(writer, fields),
            Some(span_closing_time) => writer.write_str(&span_closing_time),
        }
    }
}

impl Visit for VIMzFieldVisitor {
    fn record_debug(&mut self, field: &Field, value: &dyn Debug) {
        if field.name() == "time.busy" {
            self.span_closing_time = Some(format!("{value:?}"));
        }
    }
}
