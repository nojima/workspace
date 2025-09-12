use std::{
    collections::HashMap,
    sync::{Arc, RwLock},
};

use axum::{
    Router,
    extract::{Path, State},
    http::StatusCode,
    routing::{get, put},
};
use tokio::net::TcpListener;

type SharedState = Arc<RwLock<HashMap<String, String>>>;

async fn get_handler(
    Path(key): Path<String>,
    State(state): State<SharedState>,
) -> Result<String, StatusCode> {
    eprintln!("GET key={key:?}");

    let db = state.read().unwrap();
    match db.get(&key) {
        Some(value) => Ok(value.clone()),
        None => Err(StatusCode::NOT_FOUND),
    }
}

async fn put_handler(Path(key): Path<String>, State(state): State<SharedState>, body: String) {
    eprintln!("PUT key={key:?}");

    let mut db = state.write().unwrap();
    db.insert(key, body);
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let state: SharedState = Arc::new(RwLock::new(HashMap::new()));

    let app = Router::new()
        .route("/objects/{key}", get(get_handler))
        .route("/objects/{key}", put(put_handler))
        .with_state(Arc::clone(&state));

    let listener = TcpListener::bind("[::]:3000").await?;

    axum::serve(listener, app).await?;
    Ok(())
}
