use std::{cell::OnceCell, mem::ManuallyDrop};

pub struct Cached<T> {
    init: Box<ManuallyDrop<dyn UnsafeFnOnce<T>>>,
    value: OnceCell<T>,
}

impl<T> Cached<T> {
    pub fn new(action: impl FnOnce() -> T + 'static) -> Self {
        Self {
            init: Box::new(ManuallyDrop::new(action)),
            value: OnceCell::new(),
        }
    }

    pub fn get(&self) -> &T {
        self.value.get_or_init(|| unsafe { (*self.init).call() })
    }
}

impl<T> Drop for Cached<T> {
    fn drop(&mut self) {
        if self.value.get().is_none() {
            unsafe { ManuallyDrop::drop(&mut self.init) }
        }
    }
}

trait UnsafeFnOnce<T>: FnOnce() -> T {
    unsafe fn call(&self) -> T;
}

impl<T, F: FnOnce() -> T> UnsafeFnOnce<T> for F {
    unsafe fn call(&self) -> T {
        std::ptr::read(self)()
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
