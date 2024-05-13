use std::sync::Mutex;
use std::thread;
use std::time::Duration;

// mutable global variable
static CACHE: Mutex<Vec<String>> = Mutex::new(Vec::new());

pub fn example() {
    // writer thread
    let t1 = thread::spawn(|| {
        let mut cache = CACHE.lock().unwrap();
        cache.push("hello".to_owned());
    });
    // reader thread
    let t2 = thread::spawn(|| {
        thread::sleep(Duration::from_secs(1));
        let cache = CACHE.lock().unwrap();
        println!("{:?}", cache.first());
    });
    t1.join().unwrap();
    t2.join().unwrap();
}
