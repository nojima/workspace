use std::sync::{Arc, RwLock};

use askama::Template;
use axum::{
    extract::State,
    http::StatusCode,
    response::{Html, IntoResponse, Redirect},
    routing::{get, post},
    Router, Form,
};
use listenfd::ListenFd;
use serde::Deserialize;
use tokio::net::TcpListener;
use tower_http::services::ServeDir;

#[tokio::main]
async fn main() -> std::io::Result<()> {
    let public = ServeDir::new("public");

    let shared_state = {
        let mut app_state = AppState::default();
        app_state.comments.push(Comment {
            title: "こんにちは".to_owned(),
            body: "本文本文本文".to_owned(),
        });
        app_state.comments.push(Comment {
            title: "こんにちは2".to_owned(),
            body: "本文本文本文2".to_owned(),
        });
        Arc::new(RwLock::new(app_state))
    };

    let app = Router::new()
        .route("/hello", get(hello_handler))
        .route_service("/public", public)
        .route("/", get(index_handler))
        .route("/", post(post_comment_handler))
        .with_state(shared_state);

    let mut listenfd = ListenFd::from_env();
    let listener = match listenfd.take_tcp_listener(0).unwrap() {
        Some(listener) => TcpListener::from_std(listener)?,
        None => TcpListener::bind("[::]:3000").await?,
    };

    println!("listening on {}", listener.local_addr().unwrap());
    axum::serve(listener, app).await?;
    Ok(())
}

async fn hello_handler() -> Html<&'static str> {
    Html("<h1>Hello, World!</h1><h2>from Axum</h2>")
}

type SharedState = Arc<RwLock<AppState>>;

#[derive(Debug, Default)]
struct AppState {
    comments: Vec<Comment>,
}

#[derive(Debug)]
struct Comment {
    title: String,
    body: String,
}

#[derive(Template)]
#[template(path = "index.html")]
struct IndexTemplate<'a> {
    comments: &'a [Comment],
}

async fn index_handler(State(state): State<SharedState>) -> impl IntoResponse {
    let state = state.read().unwrap();
    let template = IndexTemplate {
        comments: &state.comments,
    };
    match template.render() {
        Ok(html) => Html(html).into_response(),
        Err(err) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("failed to render template: {err}"),
        )
            .into_response(),
    }
}

#[derive(Deserialize, Debug)]
struct PostCommentInput {
    title: String,
    body: String,
}

async fn post_comment_handler(
    State(state): State<SharedState>,
    Form(input): Form<PostCommentInput>,
) -> impl IntoResponse {
    let mut state = state.write().unwrap();
    state.comments.push(Comment {
        title: input.title,
        body: input.body,
    });
    Redirect::to("/")
}
