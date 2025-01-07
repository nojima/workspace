fn main() {
    let Some(url) = std::env::args().nth(1) else {
        panic!("No URL provided");
    };
    let response = reqwest::blocking::get(&url).unwrap();
    println!("Status code: {}", response.status());
}
