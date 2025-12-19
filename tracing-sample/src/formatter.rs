use base64::Engine;
use chrono::Utc;
use serde::ser::{SerializeMap, Serializer as _};
use std::fmt;
use tracing::field::Field;
use tracing::{Event, Subscriber};
use tracing_subscriber::registry::LookupSpan;
use tracing_subscriber::{
    Layer,
    fmt::{
        FmtContext,
        format::{self, FormatEvent, FormatFields},
    },
};

pub struct MyJsonFormatter;

impl<S, N> FormatEvent<S, N> for MyJsonFormatter
where
    S: Subscriber + for<'a> LookupSpan<'a>,
    N: for<'a> FormatFields<'a> + 'static,
{
    fn format_event(
        &self,
        ctx: &FmtContext<'_, S, N>,
        mut writer: format::Writer<'_>,
        event: &Event<'_>,
    ) -> fmt::Result {
        let mut buffer = Vec::with_capacity(256);
        let meta = event.metadata();

        let mut visit = || {
            let mut serializer = serde_json::Serializer::new(&mut buffer);
            let mut serializer = serializer.serialize_map(None)?;

            serializer.serialize_entry("logged_at", &Utc::now())?;
            serializer.serialize_entry("severity", &meta.level().as_str())?;

            if let Some(filename) = meta.file()
                && let Some(line) = meta.line()
            {
                let caller = format!("{filename}:{line}");
                serializer.serialize_entry("caller", &caller)?;
            }

            let mut visitor = tracing_serde::SerdeMapVisitor::new(serializer);
            event.record(&mut visitor);
            let mut serializer = visitor.take_serializer()?;

            let current_span = event
                .parent()
                .and_then(|id| ctx.span(id))
                .or_else(|| ctx.lookup_current());

            if let Some(current_span) = current_span {
                for span in current_span.scope() {
                    let ext = span.extensions();
                    let values = ext
                        .get::<ValuesExtension>()
                        .expect("Unable to find FieldValues in extensions");
                    for (k, v) in &values.values {
                        serializer.serialize_entry(k, &v)?;
                    }
                }
            }

            serializer.end()
        };

        visit().map_err(|_| fmt::Error)?;
        let s = str::from_utf8(&buffer).map_err(|_| fmt::Error)?;
        writeln!(writer, "{}", s)
    }
}

pub struct NopFormatter;

impl<'writer> FormatFields<'writer> for NopFormatter {
    fn format_fields<R: tracing_subscriber::field::RecordFields>(
        &self,
        _writer: format::Writer<'writer>,
        _fields: R,
    ) -> fmt::Result {
        Ok(())
    }

    fn add_fields(
        &self,
        _current: &'writer mut tracing_subscriber::fmt::FormattedFields<Self>,
        _fields: &tracing::span::Record<'_>,
    ) -> fmt::Result {
        Ok(())
    }
}

pub struct RecordFieldLayer;

impl<S> Layer<S> for RecordFieldLayer
where
    S: Subscriber + for<'a> LookupSpan<'a>,
{
    fn on_new_span(
        &self,
        attrs: &tracing::span::Attributes<'_>,
        id: &tracing::span::Id,
        ctx: tracing_subscriber::layer::Context<'_, S>,
    ) {
        let span = ctx.span(id).expect("Span not found, this is a bug");
        let values = attrs.values();

        let mut visitor = JsonVisitor {
            values: Vec::with_capacity(values.len()),
        };
        values.record(&mut visitor);

        let mut extensions = span.extensions_mut();
        if let Some(ext) = extensions.get_mut::<ValuesExtension>() {
            ext.values.extend(visitor.values);
        } else {
            extensions.insert(ValuesExtension {
                values: visitor.values,
            });
        }
    }

    fn on_record(
        &self,
        id: &tracing::span::Id,
        record: &tracing::span::Record<'_>,
        ctx: tracing_subscriber::layer::Context<'_, S>,
    ) {
        let span = ctx.span(id).expect("Span not found, this is a bug");

        let mut visitor = JsonVisitor {
            values: Vec::with_capacity(record.len()),
        };
        record.record(&mut visitor);

        let mut extensions = span.extensions_mut();
        if let Some(ext) = extensions.get_mut::<ValuesExtension>() {
            ext.values.extend(visitor.values);
        } else {
            extensions.insert(ValuesExtension {
                values: visitor.values,
            });
        }
    }
}

struct ValuesExtension {
    values: Vec<(&'static str, serde_json::Value)>,
}

struct JsonVisitor {
    values: Vec<(&'static str, serde_json::Value)>,
}

impl tracing::field::Visit for JsonVisitor {
    fn record_debug(&mut self, field: &Field, value: &dyn core::fmt::Debug) {
        if let Ok(v) = serde_json::to_value(format!("{value:?}")) {
            self.values.push((field.name(), v));
        }
    }

    fn record_f64(&mut self, field: &Field, value: f64) {
        if let Ok(v) = serde_json::to_value(value) {
            self.values.push((field.name(), v));
        }
    }

    fn record_i64(&mut self, field: &Field, value: i64) {
        if let Ok(v) = serde_json::to_value(value) {
            self.values.push((field.name(), v));
        }
    }

    fn record_u64(&mut self, field: &Field, value: u64) {
        if let Ok(v) = serde_json::to_value(value) {
            self.values.push((field.name(), v));
        }
    }

    fn record_i128(&mut self, field: &Field, value: i128) {
        if let Ok(v) = serde_json::to_value(value.to_string()) {
            self.values.push((field.name(), v));
        }
    }

    fn record_u128(&mut self, field: &Field, value: u128) {
        if let Ok(v) = serde_json::to_value(value.to_string()) {
            self.values.push((field.name(), v));
        }
    }

    fn record_bool(&mut self, field: &Field, value: bool) {
        if let Ok(v) = serde_json::to_value(value) {
            self.values.push((field.name(), v));
        }
    }

    fn record_str(&mut self, field: &Field, value: &str) {
        if let Ok(v) = serde_json::to_value(value) {
            self.values.push((field.name(), v));
        }
    }

    fn record_bytes(&mut self, field: &Field, value: &[u8]) {
        let base64_str = base64::engine::general_purpose::STANDARD_NO_PAD.encode(value);
        if let Ok(v) = serde_json::to_value(base64_str) {
            self.values.push((field.name(), v));
        }
    }

    fn record_error(&mut self, field: &Field, value: &(dyn std::error::Error + 'static)) {
        if let Ok(v) = serde_json::to_value(format!("{value:?}")) {
            self.values.push((field.name(), v));
        }
    }
}
