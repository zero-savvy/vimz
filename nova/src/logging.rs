use std::fmt::Debug;

use tracing::{
    field::{Field, Visit},
    level_filters::LevelFilter,
};
use tracing_subscriber::{
    field::RecordFields,
    fmt,
    fmt::{
        format::{DefaultFields, FmtSpan, Format, Writer},
        FormatFields,
    },
    layer::SubscriberExt,
    util::SubscriberInitExt,
    EnvFilter,
};

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

fn get_filter() -> EnvFilter {
    EnvFilter::builder()
        .with_default_directive(LevelFilter::WARN.into())
        .from_env_lossy()
        .add_directive("vimz=info".parse().unwrap())
}

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
