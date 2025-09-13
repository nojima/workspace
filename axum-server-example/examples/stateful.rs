//! ```cargo
//! [dependencies]
//! axum-server = "0.7"
//! hyper = "1"
//! tokio = { version = "1", features = ["rt-multi-thread", "macros"] }
//! tower = { version = "0.5", features = ["make", "util"] }
//! ```
use std::{
    convert::Infallible,
    net::SocketAddr,
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
};

use hyper::{Request, Response, body::Incoming};
use tower::make::Shared;

struct RequestHandler {
    message: String,
    count: AtomicUsize,
}

impl RequestHandler {
    async fn handle(
        self: Arc<Self>,
        req: Request<Incoming>,
    ) -> Result<Response<String>, Infallible> {
        eprintln!("HTTP request received: {req:?}");
        let count = self.count.fetch_add(1, Ordering::SeqCst);
        let text = format!("{}: count={}", self.message, count);
        Ok(Response::new(text))
    }
}

#[tokio::main]
async fn main() {
    let request_handler = Arc::new(RequestHandler {
        message: "Hello, World".to_owned(),
        count: AtomicUsize::new(0),
    });

    let make_service = Shared::new(tower::service_fn(move |req| {
        Arc::clone(&request_handler).handle(req)
    }));

    let addr = SocketAddr::from(([0, 0, 0, 0], 3000));
    eprintln!("Start HTTP server on {addr:?}");
    axum_server::bind(addr).serve(make_service).await.unwrap();
}
