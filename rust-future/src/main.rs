use futures::future; // 追加！

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

async fn http_get(url: &str) -> Result<String> {
    let resp = reqwest::get(url).await?;
    let body = resp.text().await?;
    Ok(body)
}

#[tokio::main]
async fn main() -> Result<()> {
    let fut1 = http_get("https://httpbin.org/delay/5");
    let fut2 = http_get("https://httpbin.org/delay/5");

    // join を使ってふたつの Future を同時に待つ
    let (body1, body2) = futures::try_join!(fut1, fut2)?;

    println!("body1 = {}", body1);
    println!("body2 = {}", body2);
    Ok(())
}
