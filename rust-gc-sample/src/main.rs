use gc::{Finalize, Gc, GcCell, Trace};

#[derive(Trace, Finalize)]
struct Node {
    prev: GcCell<Option<Gc<Node>>>,
    next: GcCell<Option<Gc<Node>>>,
    value: String,
}

#[derive(Trace, Finalize)]
struct DoublyLinkedList {
    head: Option<Gc<Node>>,
    tail: Option<Gc<Node>>,
}

impl DoublyLinkedList {
    fn new() -> Self {
        Self { head: None, tail: None }
    }

    fn push(&mut self, value: String) {
        match &self.tail {
            None => {
                let node = Gc::new(Node {
                    prev: GcCell::new(None),
                    next: GcCell::new(None),
                    value,
                });
                self.head = Some(node.clone());
                self.tail = Some(node);
            }
            Some(tail) => {
                let node = Gc::new(Node {
                    prev: GcCell::new(Some(tail.clone())),
                    next: GcCell::new(None),
                    value,
                });
                *tail.next.borrow_mut() = Some(node.clone());
                self.tail = Some(node);
            }
        }
    }

    fn iterate_forward(&self, mut f: impl FnMut(&str)) {
        let mut p = self.head.clone();
        while let Some(node) = p {
            f(&node.value);
            p = node.next.borrow().clone();
        }
    }

    fn iterate_backward(&self, mut f: impl FnMut(&str)) {
        let mut p = self.tail.clone();
        while let Some(node) = p {
            f(&node.value);
            p = node.prev.borrow().clone();
        }
    }
}

fn main() {
    let mut list = DoublyLinkedList::new();

    for value in &vec!["foo", "bar", "fizz", "buzz"] {
        list.push(value.to_string());
    }

    println!("Iterate forward:");
    list.iterate_forward(|value| println!("  {}", value));

    println!("Iterate backward:");
    list.iterate_backward(|value| println!("  {}", value));
}
