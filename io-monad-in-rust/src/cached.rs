use std::cell::{Cell, OnceCell};

pub struct Cached<'a, T> {
    init: Cell<Option<Box<dyn FnOnce() -> T + 'a>>>,
    value: OnceCell<T>,
}

impl<'a, T> Cached<'a, T> {
    pub fn new(init: impl FnOnce() -> T + 'a) -> Self {
        Self {
            init: Cell::new(Some(Box::new(init))),
            value: OnceCell::new(),
        }
    }

    pub fn get(&self) -> &T {
        self.value.get_or_init(|| {
            let Some(init) = self.init.take() else {
                unreachable!("The init function should be never called twice");
            };
            init()
        })
    }

    pub fn take(self) -> T {
        let _ = self.get();
        let Some(value) = self.value.into_inner() else {
            unreachable!("The value should be always cached after calling get()");
        };
        value
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cached() {
        let mut n_called = 0;
        let cached = Cached::new(|| {
            n_called += 1;
            "hello".to_string()
        });
        assert_eq!(cached.get(), "hello");
        assert_eq!(cached.get(), "hello");
        assert_eq!(cached.get(), "hello");
        drop(cached);
        assert_eq!(n_called, 1);
    }
}
