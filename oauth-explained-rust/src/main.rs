use anyhow::anyhow;
use axum::{
    error_handling::HandleErrorLayer,
    extract::Query,
    http::StatusCode,
    response::{Html, IntoResponse, Redirect, Response},
    routing::get,
    BoxError, Router,
};
use base64::{prelude::BASE64_STANDARD_NO_PAD, Engine};
use serde::{Deserialize, Serialize};
use std::io;
use tower::ServiceBuilder;
use tower_sessions::{MemoryStore, Session, SessionManagerLayer};
use url::Url;

const SESSION_COOKIE_NAME: &str = "session_id";

const CLIENT_ID: &str = "oidc-test";
// コンパイル時に環境変数 OIDC_CLIENT_SECRET から client secret を取得する
const CLIENT_SECRET: &str = std::env!("OIDC_CLIENT_SECRET");
const BASE_URL: &str = "http://localhost:3000/";
const CALLBACK_URL: &str = "http://localhost:3000/oauth2/callback";
const AUTHORIZE_URL: &str = "http://localhost:8080/realms/master/protocol/openid-connect/auth";
const TOKEN_URL: &str = "http://localhost:8080/realms/master/protocol/openid-connect/token";

#[tokio::main]
async fn main() -> io::Result<()> {
    let session_store = MemoryStore::default();
    let session_service = ServiceBuilder::new()
        .layer(HandleErrorLayer::new(|_: BoxError| async {
            StatusCode::BAD_REQUEST
        }))
        .layer(
            SessionManagerLayer::new(session_store)
                .with_secure(false)
                .with_name(SESSION_COOKIE_NAME),
        );

    let app = Router::new()
        .route("/", get(root_handler))
        .route("/login", get(login_handler))
        .route("/oauth2/callback", get(oauth2_callback_handler))
        .layer(session_service);

    let listener = tokio::net::TcpListener::bind("[::]:3000").await?;
    eprintln!("listening on {}", listener.local_addr()?);

    axum::serve(listener, app).await?;
    Ok(())
}

async fn root_handler(session: Session) -> Result<Response, AppError> {
    match session.get::<String>("user_id").await? {
        Some(user_id) => {
            let email = session.get::<String>("email").await?.unwrap_or_default();
            let body = format!(
                "<h3>Logged In</h3><p>UserID: {}</p><p>Email: {}</p>",
                user_id, email
            );
            Ok(Html(body).into_response())
        }
        None => {
            let body = "<h3><a href='/login'>Login</a></h3>";
            Ok(Html(body).into_response())
        }
    }
}

async fn login_handler(session: Session) -> Result<Redirect, AppError> {
    session.delete().await?;

    let state = {
        let mut state_buf = [0u8; 16];
        getrandom::getrandom(&mut state_buf).unwrap();
        BASE64_STANDARD_NO_PAD.encode(&state_buf)
    };
    session.insert("state", &state).await?;

    let params = [
        ("response_type", "code"),
        ("client_id", CLIENT_ID),
        ("redirect_uri", CALLBACK_URL),
        ("scope", "openid email"),
        ("state", &state),
    ];
    let location = Url::parse_with_params(AUTHORIZE_URL, &params)?;
    Ok(Redirect::to(location.as_str()))
}

#[derive(Debug, Deserialize)]
struct OAuth2CallbackInput {
    code: String,
    state: String,
}

#[derive(Debug, Serialize)]
struct TokenRequest {
    grant_type: String,
    client_id: String,
    client_secret: String,
    redirect_uri: String,
    code: String,
}

#[derive(Debug, Deserialize)]
struct TokenResponse {
    access_token: String,
    id_token: String,
}

#[derive(Debug, Deserialize)]
struct UserInfo {
    #[serde(rename = "sub")]
    user_id: String,
    #[serde(rename = "email")]
    email: Option<String>,
}

async fn oauth2_callback_handler(
    session: Session,
    Query(query): Query<OAuth2CallbackInput>,
) -> Result<Redirect, AppError> {
    // state の値がセッションに保存されているものと同一か確認する
    let Some(stored_state) = session.get::<String>("state").await? else {
        return Err(anyhow!("state not found in the session").into());
    };
    if query.state != stored_state {
        let location = Url::parse_with_params(BASE_URL, [("error", "invalid_state")])?;
        return Ok(Redirect::to(location.as_str()));
    }


    let params = TokenRequest {
        grant_type: "authorization_code".to_string(),
        client_id: CLIENT_ID.to_string(),
        client_secret: CLIENT_SECRET.to_string(),
        redirect_uri: CALLBACK_URL.to_string(),
        code: query.code,
    };

    let http_client = reqwest::Client::new();
    let resp = http_client.post(TOKEN_URL).form(&params).send().await?;
    eprintln!("oauth2_callback_handler: resp={:?}", resp);

    let resp_status = resp.status();
    let resp_body = resp.text().await?;
    eprintln!("oauth2_callback_handler: resp_body={}", resp_body);

    if !resp_status.is_success() {
        return Err(anyhow!("failed to get token from IdP").into());
    }

    let token_resp: TokenResponse = serde_json::from_str(&resp_body)?;

    let Some(jwt) = token_resp.id_token.split('.').nth(1) else {
        return Err(anyhow!("invalid JWT format").into());
    };
    let user_info: UserInfo = {
        let b = BASE64_STANDARD_NO_PAD.decode(jwt.as_bytes())?;
        serde_json::from_slice(&b)?
    };

    session.insert("user_id", &user_info.user_id).await?;
    session.insert("email", &user_info.email).await?;
    session
        .insert("access_token", &token_resp.access_token)
        .await?;
    session.insert("id_token", &token_resp.id_token).await?;

    Ok(Redirect::to(BASE_URL))
}

struct AppError(anyhow::Error);

// AppError から Response への変換を定義する。
// これにより、AppError を handler の戻り値として使えるようになる。
impl IntoResponse for AppError {
    fn into_response(self) -> Response {
        (StatusCode::INTERNAL_SERVER_ERROR, self.0.to_string()).into_response()
    }
}

// anyhow::Error に変換できるエラーは AppError にも変換できるようにする。
// これにより `?` オペレータで AppError を簡単に返すことができる。
impl<E> From<E> for AppError
where
    E: Into<anyhow::Error>,
{
    fn from(err: E) -> Self {
        Self(err.into())
    }
}
