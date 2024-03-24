use std::cell::{Cell, OnceCell};

pub struct Cached<T> {
    init: Cell<Option<Box<dyn FnOnce() -> T>>>,
    value: OnceCell<T>,
}

impl<T> Cached<T> {
    pub fn new(init: impl FnOnce() -> T + 'static) -> Self {
        Self {
            init: Cell::new(Some(Box::new(init))),
            value: OnceCell::new(),
        }
    }

    pub fn get(&self) -> &T {
        self.value.get_or_init(|| {
            let Some(init) = self.init.take() else {
                panic!("[bug] init function called twice!")
            };
            init()
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug)]
    struct Foo {
        #[allow(dead_code)]
        message: String,
    }

    impl Drop for Foo {
        fn drop(&mut self) {
            println!("Dropped: {self:?}")
        }
    }

    #[test]
    fn test() {
        let msg = "hello".to_owned();
        let c1 = Cached::new(|| Foo { message: msg });
        let msg2 = "hello".to_owned();
        let _c2 = Cached::new(|| Foo { message: msg2 });
        println!("{:?} world", c1.get());
        println!("{:?} world again", c1.get());
    }
}
