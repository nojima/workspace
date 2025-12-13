use tracing::{Level, event, instrument, span};

fn main() {
    tracing_subscriber::fmt().init();

    event!(Level::INFO, "event 1");
    foo();

    let _span1 = span!(Level::INFO, "span 1").entered();
    event!(Level::INFO, "event 2");

    let _span2 = span!(Level::INFO, "span 2").entered();
    event!(Level::INFO, "event 3");
}

#[instrument]
fn foo() {
    event!(Level::INFO, "foo called");
}
