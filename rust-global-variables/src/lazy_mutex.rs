use std::collections::HashMap;
use std::sync::Mutex;
use std::thread;
use std::time::Duration;
use once_cell::sync::Lazy;

// global mutable variable
static CACHE: Lazy<Mutex<HashMap<String, String>>> =
    Lazy::new(|| Mutex::new(HashMap::new()));

pub fn example() {
    // writer thread
    let t1 = thread::spawn(|| {
        let mut cache = CACHE.lock().unwrap();
        cache.insert("hello".to_owned(), "world".to_owned());
    });
    // reader thread
    let t2 = thread::spawn(|| {
        thread::sleep(Duration::from_secs(1));
        let cache = CACHE.lock().unwrap();
        println!("{:?}", cache.get("hello"));
    });
    t1.join().unwrap();
    t2.join().unwrap();
}
