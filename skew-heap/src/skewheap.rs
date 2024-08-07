use std::mem::swap;

pub struct SkewHeap<T: Ord> {
    root: Option<Box<Node<T>>>,
}

impl<T: Ord> SkewHeap<T> {
    pub fn new() -> Self {
        Self { root: None }
    }

    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    pub fn push(&mut self, value: T) {
        self.root = Node::merge(self.root.take(), Node::singleton(value));
    }

    pub fn pop_min(&mut self) -> Option<T> {
        let root = self.root.take()?;
        let x = root.value;
        self.root = Node::merge(root.l, root.r);
        Some(x)
    }
}

pub struct Node<T: Ord> {
    value: T,
    l: Option<Box<Node<T>>>,
    r: Option<Box<Node<T>>>,
}

impl<T: Ord> Node<T> {
    pub fn singleton(value: T) -> Option<Box<Node<T>>> {
        Some(Box::new(Node {
            value,
            l: None,
            r: None,
        }))
    }

    /*
    pub fn merge(a: Option<Box<Node<T>>>, b: Option<Box<Node<T>>>) -> Option<Box<Node<T>>> {
        match (a, b) {
            (None, b) => b,
            (a, None) => a,
            (Some(a), Some(b)) => {
                let (mut a, b) = if a.value < b.value { (a, b) } else { (b, a) };
                a.r = Self::merge(a.r, Some(b));
                swap(&mut a.l, &mut a.r);
                Some(a)
            }
        }
    }
    */

    pub fn merge(mut a: Option<Box<Node<T>>>, mut b: Option<Box<Node<T>>>) -> Option<Box<Node<T>>> {
        let mut stack = Vec::new();
        let mut ret = loop {
            match (a, b) {
                (None, b) => break b,
                (a, None) => break a,
                (Some(x), Some(y)) => {
                    let (mut x, y) = if x.value < y.value { (x, y) } else { (y, x) };
                    let r = x.r.take();
                    stack.push(x);
                    a = r;
                    b = Some(y);
                }
            }
        };
        while let Some(mut x) = stack.pop() {
            x.r = ret;
            swap(&mut x.l, &mut x.r);
            ret = Some(x);
        }
        ret
    }
}

#[cfg(test)]
mod tests {
    use crate::skewheap::SkewHeap;

    #[test]
    fn test_skew_heap() {
        let mut heap = SkewHeap::new();
        for x in [
            1, 1, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 7, 8, 8, 9, 9, 9,
        ] {
            heap.push(x);
        }
        let mut v = Vec::new();
        while !heap.is_empty() {
            let x = heap.pop_min();
            let Some(x) = x else {
                panic!("pop_min should return Some(x)");
            };
            v.push(x);
        }
        assert_eq!(
            v,
            vec![1, 1, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 7, 8, 8, 9, 9, 9]
        );
    }
}
