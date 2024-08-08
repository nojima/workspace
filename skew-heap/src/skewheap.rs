use std::mem::swap;

pub enum SkewHeap<T: Ord> {
    Empty,
    Node(SkewNode<T>),
}

pub struct SkewNode<T: Ord> {
    x: T,
    l: Box<SkewHeap<T>>,
    r: Box<SkewHeap<T>>,
}

impl<T: Ord> SkewHeap<T> {
    pub fn singleton(x: T) -> SkewHeap<T> {
        Self::Node(SkewNode {
            x,
            l: Box::new(Self::Empty),
            r: Box::new(Self::Empty),
        })
    }

    pub fn is_empty(&self) -> bool {
        match self {
            Self::Empty => true,
            _ => false,
        }
    }

    pub fn push(self, x: T) -> SkewHeap<T> {
        Self::merge(self, Self::singleton(x))
    }

    pub fn pop_min(self) -> (Option<T>, SkewHeap<T>) {
        match self {
            Self::Empty => (None, self),
            Self::Node(node) => (Some(node.x), Self::merge(*node.l, *node.r)),
        }
    }

    pub fn merge(a: SkewHeap<T>, b: SkewHeap<T>) -> SkewHeap<T> {
        use SkewHeap::*;
        match (a, b) {
            (Empty, b) => b,
            (a, Empty) => a,
            (Node(mut a), Node(mut b)) => {
                if a.x > b.x {
                    swap(&mut a, &mut b);
                }
                a.r = Box::new(Self::merge(*a.r, Node(b)));
                swap(&mut a.l, &mut a.r);
                Node(a)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_skew_heap() {
        use super::SkewHeap;
        let mut heap = SkewHeap::Empty;
        for x in [1, 1, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 7, 8, 8, 9, 9, 9] {
            heap = heap.push(x);
        }
        let mut v = Vec::new();
        while !heap.is_empty() {
            let (x, h) = heap.pop_min();
            let Some(x) = x else {
                panic!("pop_min should return Some(x)");
            };
            heap = h;
            v.push(x);
        }
        assert_eq!(v, vec![1, 1, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 7, 8, 8, 9, 9, 9]);
    }
}
