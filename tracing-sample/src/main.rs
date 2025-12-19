mod formatter;

use tracing::{Level, event, instrument, span};
use tracing_subscriber::{Layer, layer::SubscriberExt};

use crate::formatter::{MyJsonFormatter, NopFormatter, RecordFieldLayer};

fn main() {
    let layer = tracing_subscriber::fmt::layer()
        .event_format(MyJsonFormatter)
        .fmt_fields(NopFormatter)
        .and_then(RecordFieldLayer);
    let subscriber = tracing_subscriber::registry().with(layer);
    tracing::subscriber::set_global_default(subscriber).unwrap();

    event!(Level::INFO, "event 1");
    foo();

    let _span1 = span!(Level::INFO, "span 1", foo = "FOO", foobar = true).entered();
    event!(Level::INFO, "event 2");

    let _span2 = span!(Level::INFO, "span 2", bar = 42).entered();
    event!(Level::INFO, "event 3");

    event!(Level::DEBUG, "debug event");
}

#[instrument]
fn foo() {
    event!(Level::INFO, "foo called");
}
