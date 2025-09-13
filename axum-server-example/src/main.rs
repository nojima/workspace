use std::{convert::Infallible, net::SocketAddr, time::Duration};

use axum_server::Handle;
use hyper::{Request, Response, body::Incoming};

#[tokio::main]
async fn main() {
    let make_service = tower::service_fn(async |_: SocketAddr| -> Result<_, Infallible> {
        Ok(tower::service_fn(hello_handler))
    });

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

async fn hello_handler(req: Request<Incoming>) -> Result<Response<String>, Infallible> {
    eprintln!("HTTP request received: {req:?}");
    Ok(Response::new("Hello, World!".to_owned()))
}

async fn signal_handler(handle: Handle) {
    tokio::signal::ctrl_c().await.unwrap();
    eprintln!("SIGINT received!");
    handle.graceful_shutdown(Some(Duration::from_secs(10)));
}
