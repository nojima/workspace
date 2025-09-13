//! ```cargo
//! [dependencies]
//! axum-server = "0.7"
//! hyper = "1"
//! tokio = { version = "1", features = ["rt-multi-thread", "signal", "macros"] }
//! tower = { version = "0.5", features = ["make", "util"] }
//! ```
use std::{convert::Infallible, net::SocketAddr, time::Duration};

use axum_server::Handle;
use hyper::{Request, Response, body::Incoming};
use tower::make::Shared;

async fn request_handler(req: Request<Incoming>) -> Result<Response<String>, Infallible> {
    eprintln!("HTTP request received: {req:?}");
    Ok(Response::new("Hello, World!".to_owned()))
}

async fn signal_handler(handle: Handle) {
    tokio::signal::ctrl_c().await.unwrap();
    eprintln!("SIGINT received!");
    handle.graceful_shutdown(Some(Duration::from_secs(10)));
}

#[tokio::main]
async fn main() {
    let make_service = Shared::new(tower::service_fn(request_handler));

    let handle = Handle::new();
    tokio::spawn(signal_handler(handle.clone()));

    let addr = SocketAddr::from(([0, 0, 0, 0], 3000));
    eprintln!("Start HTTP server on {addr:?}");
    axum_server::bind(addr)
        .handle(handle)
        .serve(make_service)
        .await
        .unwrap();
}
