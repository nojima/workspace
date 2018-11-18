extern crate rand;

use std::mem;
use std::cmp::Ordering;
use std::fmt;
use rand::prelude::*;

struct BinaryNode<K: Ord> {
    key: K,
    lhs: Option<Box<BinaryNode<K>>>,
    rhs: Option<Box<BinaryNode<K>>>,
}

impl<K: Ord> BinaryNode<K> {
    fn new(key: K) -> Self {
        Self {
            key,
            lhs: Option::None,
            rhs: Option::None,
        }
    }
}

struct SplayTree<K: Ord> {
    root: Option<Box<BinaryNode<K>>>,
}

impl<K: Ord> SplayTree<K> {
    fn new() -> Self {
        Self {
            root: Option::None,
        }
    }

    fn insert(&mut self, key: K) -> bool {
        let root = mem::replace(&mut self.root, None);
        let root = splay(&key, root);
        if root.is_none() {
            self.root = Some(Box::new(BinaryNode::new(key)));
            return true;
        }
        let mut root = root.unwrap();
        match key.cmp(&root.key) {
            Ordering::Equal => {
                // 既に同じキーを持つ要素が存在する
                self.root = Some(root);
                false
            }
            Ordering::Less => {
                self.root = Some(Box::new(BinaryNode{
                    key,
                    lhs: mem::replace(&mut root.lhs, None),
                    rhs: Some(root),
                }));
                true
            }
            Ordering::Greater => {
                self.root = Some(Box::new(BinaryNode{
                    key,
                    rhs: mem::replace(&mut root.rhs, None),
                    lhs: Some(root),
                }));
                true
            }
        }
    }

    fn search(&mut self, key: K) -> bool {
        let root = mem::replace(&mut self.root, None);
        match splay(&key, root) {
            Some(root) => {
                let ret = root.key == key;
                self.root = Some(root);
                ret
            }
            None => false,
        }
    }

}

impl<K: Ord + fmt::Debug> SplayTree<K> {
    fn pretty_print(&self) {
        pretty_print(&self.root, 0);
    }
}

fn pretty_print<K: Ord + fmt::Debug>(node: &Option<Box<BinaryNode<K>>>, indent: usize) {
    match node {
        Some(ref node) => {
            pretty_print(&node.lhs, indent + 2);
            println!("{}{:?}", " ".repeat(indent * 2), node.key);
            pretty_print(&node.rhs, indent + 2);
        }
        None => {}
    }
}

// node を根とする部分木に対してスプレー操作を実行し、新たな根を返す。
// key を持つノードが部分木に存在する場合、それが新たな根となる。
// key が部分木に存在しない場合、最後にアクセスしたノードが根となる。
// 部分木は破壊的に変更される。
fn splay<K: Ord>(key: &K, node: Option<Box<BinaryNode<K>>>) -> Option<Box<BinaryNode<K>>> {
    if node.is_none() { return None; }
    let node = node.unwrap();

    let new_node = match key.cmp(&node.key) {
        Ordering::Less => zig_left(key, node),
        Ordering::Greater => zig_right(key, node),
        Ordering::Equal => node,
    };
    Some(new_node)
}

fn rotate_right<K: Ord>(mut node: Box<BinaryNode<K>>) -> Box<BinaryNode<K>> {
    let mut x = node.lhs.unwrap();
    node.lhs = x.rhs;
    x.rhs = Option::Some(node);
    x
}

fn rotate_left<K: Ord>(mut node: Box<BinaryNode<K>>) -> Box<BinaryNode<K>> {
    let mut x = node.rhs.unwrap();
    node.rhs = x.lhs;
    x.lhs = Option::Some(node);
    x
}

fn zig_left<K: Ord>(key: &K, mut node: Box<BinaryNode<K>>) -> Box<BinaryNode<K>> {
    if node.lhs.is_none() { return node }
    let mut lhs = node.lhs.unwrap();

    if key < &lhs.key {
        // zig-zig

        // left-left の部分木の根に key を持ってくる 
        lhs.lhs = splay(key, lhs.lhs);
        node.lhs = Some(lhs);

        // 右回転を２回行って left-left を根に持ってくる
        let new_node = rotate_right(node);
        if new_node.lhs.is_some() {
            rotate_right(new_node)
        } else {
            new_node
        }
    } else if key > &lhs.key {
        // zig-zag

        // left-right の部分木の根に key を持ってくる
        lhs.rhs = splay(key, lhs.rhs);

        // 左回転と右回転を行って left-right を根に持ってくる
        node.lhs = if lhs.rhs.is_some() {
            Some(rotate_left(lhs))
        } else {
            Some(lhs)
        };
        rotate_right(node)
    } else {
        node.lhs = Some(lhs);
        rotate_right(node)
    }
}

fn zig_right<K: Ord>(key: &K, mut node: Box<BinaryNode<K>>) -> Box<BinaryNode<K>> {
    if node.rhs.is_none() { return node }
    let mut rhs = node.rhs.unwrap();

    if key > &rhs.key {
        // zig-zig

        // right-right の部分木の根に key を持ってくる 
        rhs.rhs = splay(key, rhs.rhs);
        node.rhs = Some(rhs);

        // 左回転を２回行って left-left を根に持ってくる
        let new_node = rotate_left(node);
        if new_node.rhs.is_some() {
            rotate_left(new_node)
        } else {
            new_node
        }
    } else if key < &rhs.key {
        // zig-zag

        // right-left の部分木の根に key を持ってくる
        rhs.lhs = splay(key, rhs.lhs);

        // 右回転と左回転を行って right-left を根に持ってくる
        node.rhs = if rhs.lhs.is_some() {
            Some(rotate_right(rhs))
        } else {
            Some(rhs)
        };
        rotate_left(node)
    } else {
        node.rhs = Some(rhs);
        rotate_left(node)
    }
}

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