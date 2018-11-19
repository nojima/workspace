extern crate rand;

use std::mem;
use std::cmp::Ordering;
use std::fmt;
use rand::prelude::*;

struct BinaryNode<K: Ord> {
    key: K,
    left: Option<Box<BinaryNode<K>>>,
    right: Option<Box<BinaryNode<K>>>,
}

impl<K: Ord> BinaryNode<K> {
    fn new(key: K) -> Self {
        Self {
            key,
            left: Option::None,
            right: Option::None,
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
                    left: mem::replace(&mut root.left, None),
                    right: Some(root),
                }));
                true
            }
            Ordering::Greater => {
                self.root = Some(Box::new(BinaryNode{
                    key,
                    right: mem::replace(&mut root.right, None),
                    left: Some(root),
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
            pretty_print(&node.left, indent + 2);
            println!("{}{:?}", " ".repeat(indent * 2), node.key);
            pretty_print(&node.right, indent + 2);
        }
        None => {}
    }
}

// root を根とする部分木に対してスプレー操作を実行し、新たな根を返す。
// key を持つノードが部分木に存在する場合、それが新たな根となる。
// key が部分木に存在しない場合、最後にアクセスしたノードが根となる。
// 部分木は破壊的に変更される。
fn splay<K: Ord>(key: &K, root: Option<Box<BinaryNode<K>>>) -> Option<Box<BinaryNode<K>>> {
    if root.is_none() { return None; }
    let node = root.unwrap();

    let new_node = match key.cmp(&node.key) {
        Ordering::Less => zig_left(key, node),
        Ordering::Greater => zig_right(key, node),
        Ordering::Equal => node,
    };
    Some(new_node)
}

// root の左側のノードが新たな根となるように木を回転させ、新たな根を返す。
fn rotate_right<K: Ord>(mut root: Box<BinaryNode<K>>) -> Box<BinaryNode<K>> {
    let mut x = root.left.unwrap();
    root.left = x.right;
    x.right = Option::Some(root);
    x
}

// root の右側のノードが新たな根となるように木を回転させ、新たな根を返す。
fn rotate_left<K: Ord>(mut root: Box<BinaryNode<K>>) -> Box<BinaryNode<K>> {
    let mut x = root.right.unwrap();
    root.right = x.left;
    x.left = Option::Some(root);
    x
}

fn zig_left<K: Ord>(key: &K, mut root: Box<BinaryNode<K>>) -> Box<BinaryNode<K>> {
    if root.left.is_none() { return root }
    let mut left = root.left.unwrap();

    if key < &left.key {
        // zig-zig

        // left-left の部分木の根に key を持ってくる 
        left.left = splay(key, left.left);
        root.left = Some(left);

        // 右回転を２回行って left-left を根に持ってくる
        let new_node = rotate_right(root);
        if new_node.left.is_some() {
            rotate_right(new_node)
        } else {
            new_node
        }
    } else if key > &left.key {
        // zig-zag

        // left-right の部分木の根に key を持ってくる
        left.right = splay(key, left.right);

        // 左回転と右回転を行って left-right を根に持ってくる
        root.left = if left.right.is_some() {
            Some(rotate_left(left))
        } else {
            Some(left)
        };
        rotate_right(root)
    } else {
        // zig
        root.left = Some(left);
        rotate_right(root)
    }
}

fn zig_right<K: Ord>(key: &K, mut root: Box<BinaryNode<K>>) -> Box<BinaryNode<K>> {
    if root.right.is_none() { return root }
    let mut right = root.right.unwrap();

    if key > &right.key {
        // zig-zig

        // right-right の部分木の根に key を持ってくる 
        right.right = splay(key, right.right);
        root.right = Some(right);

        // 左回転を２回行って left-left を根に持ってくる
        let new_node = rotate_left(root);
        if new_node.right.is_some() {
            rotate_left(new_node)
        } else {
            new_node
        }
    } else if key < &right.key {
        // zig-zag

        // right-left の部分木の根に key を持ってくる
        right.left = splay(key, right.left);

        // 右回転と左回転を行って right-left を根に持ってくる
        root.right = if right.left.is_some() {
            Some(rotate_right(right))
        } else {
            Some(right)
        };
        rotate_left(root)
    } else {
        // zig
        root.right = Some(right);
        rotate_left(root)
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