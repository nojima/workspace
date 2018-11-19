extern crate rand;
mod splay_tree;

use rand::prelude::*;
use self::splay_tree::*;

fn main() {
    let mut tree = SplayTree::new();

    for _i in 0..100 {
        let x: i8 = random();
        println!("------------------");
        println!("Insert: {}", x);
        tree.insert(x);
        tree.pretty_print();

        let y: i8 = random();
        println!("------------------");
        let res = tree.search(y);
        println!("Search: {}, found={}", y, res);
        tree.pretty_print();
    }
}

#[test]
fn test_insert_and_find() {
    let mut tree = SplayTree::new();

    assert_eq!(tree.insert(3), true);
    assert_eq!(tree.insert(1), true);
    assert_eq!(tree.insert(4), true);
    assert_eq!(tree.insert(1), false);
    assert_eq!(tree.insert(5), true);
    assert_eq!(tree.insert(9), true);

    assert_eq!(tree.search(2), false);
    assert_eq!(tree.search(6), false);
    assert_eq!(tree.search(5), true);
    assert_eq!(tree.search(3), true);
    assert_eq!(tree.search(5), true);
}
