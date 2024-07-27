use std::{cmp::min, mem::swap};

struct Node<V: Ord> {
    value: V,
    left: Option<Box<Node<V>>>,
    right: Option<Box<Node<V>>>,
    rank: usize,
}

impl<V: Ord> Node<V> {
    // 単一のノードからなるヒープ(の根)を返す。
    fn singleton(value: V) -> Option<Box<Node<V>>> {
        Some(Box::new(Node {
            value,
            left: None,
            right: None,
            rank: 1,
        }))
    }

    // a, b をそれぞれ根とするふたつのヒープをマージする。
    // O(log n)
    fn merge(a: Option<Box<Node<V>>>, b: Option<Box<Node<V>>>) -> Option<Box<Node<V>>> {
        match (a, b) {
            (None, b) => b,
            (a, None) => a,
            (Some(a), Some(b)) => {
                // a のほうが値が小さくなるように変数を置きなおす。
                // すると a がマージ後の木の親となるノードとなる。
                let (mut a, b) = if a.value < b.value { (a, b) } else { (b, a) };
                // a.right に b をマージする。
                a.right = Self::merge(a.right, Some(b));
                // leftist property が破れていたら swap して修復する。
                // leftist property:
                //   任意のノード x について x.left.rank ≧ x.right.rank
                let rank_l = a.left.as_ref().map_or(0, |l| l.rank);
                let rank_r = a.right.as_ref().map_or(0, |r| r.rank);
                if rank_l < rank_r {
                    swap(&mut a.left, &mut a.right);
                }
                // ランクを更新する。
                a.rank = min(rank_l, rank_r) + 1;
                Some(a)
            }
        }
    }
}

// leftist heap によって実装された優先度付きキュー。
pub struct LeftistHeap<V: Ord> {
    root: Option<Box<Node<V>>>,
}

impl<V: Ord> LeftistHeap<V> {
    // 空のヒープを作成する。
    // O(1)
    pub fn new() -> Self {
        Self { root: None }
    }

    // 空であれば真を返す。
    // O(1)
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    // ヒープに value を追加する。
    // O(log n)
    pub fn push(&mut self, value: V) {
        self.root = Node::merge(self.root.take(), Node::singleton(value))
    }

    // ヒープから最小の値を取り除いて、それを返す。
    // O(log n)
    pub fn pop_min(&mut self) -> Option<V> {
        let Some(root) = self.root.take() else {
            return None;
        };
        let value = root.value;
        self.root = Node::merge(root.left, root.right);
        Some(value)
    }

    // ふたつのヒープをマージする。
    // O(log n)
    pub fn merge(a: LeftistHeap<V>, b: LeftistHeap<V>) -> LeftistHeap<V> {
        LeftistHeap {
            root: Node::merge(a.root, b.root),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::LeftistHeap;

    #[test]
    fn basic_test() {
        let mut heap = LeftistHeap::new();

        // push
        for v in [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] {
            heap.push(v)
        }

        // pop_min
        let mut got = Vec::new();
        while !heap.is_empty() {
            got.push(heap.pop_min().unwrap());
        }

        // verify
        let want = vec![1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9];
        assert_eq!(want, got);
    }
}
