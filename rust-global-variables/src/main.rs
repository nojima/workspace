mod bare_mutex;
mod lazy_mutex;
mod once_cell_mutex;

fn main() {
    println!("bare_mutex:");
    bare_mutex::example();
    println!("lazy_mutex:");
    lazy_mutex::example();
    println!("once_cell_mutex:");
    once_cell_mutex::example();
}
