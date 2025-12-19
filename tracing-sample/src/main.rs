mod formatter;

use core::f64;

use tracing::{Level, event, instrument, span};
use tracing_subscriber::{Layer, layer::SubscriberExt, util::SubscriberInitExt};

use crate::formatter::{MyJsonFormatter, NopFormatter, RecordFieldLayer};

fn main() {
    let layer = tracing_subscriber::fmt::layer()
        .event_format(MyJsonFormatter)
        .fmt_fields(NopFormatter)
        .and_then(RecordFieldLayer);
    tracing_subscriber::registry().with(layer).init();

    event!(Level::INFO, "event 1");
    foo(123);

    let trace_id = 1111111111111111111111u128;
    let bytes = b"some bytes";

    let _span1 = span!(
        Level::INFO,
        "span 1",
        foo = "FOO",
        foobar = true,
        trace_id = trace_id,
        bytes = &bytes[..],
    )
    .entered();

    let binary = b"hoge hoge";
    event!(Level::INFO, binary = &binary[..], "event 2");

    let _span2 = span!(Level::INFO, "span 2", bar = 42, pi = f64::consts::PI).entered();
    event!(Level::INFO, "event 3");

    event!(Level::DEBUG, "debug event");

    log::info!("Hello from log crate");
}

#[instrument]
fn foo(_i: u32) {
    event!(Level::INFO, "foo called");
}
