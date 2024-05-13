use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};
use std::thread;
use std::time::Duration;

// global mutable variable
static CACHE: OnceLock<Mutex<HashMap<String, String>>> = OnceLock::new();

fn get_cache() -> &'static Mutex<HashMap<String, String>> {
    CACHE.get_or_init(|| Mutex::new(HashMap::new()))
}

pub fn example() {
    // writer thread
    let t1 = thread::spawn(|| {
        let mut cache = get_cache().lock().unwrap();
        cache.insert("hello".to_owned(), "world".to_owned());
    });
    // reader thread
    let t2 = thread::spawn(|| {
        thread::sleep(Duration::from_secs(1));
        let cache = get_cache().lock().unwrap();
        println!("{:?}", cache.get("hello"));
    });
    t1.join().unwrap();
    t2.join().unwrap();
}
