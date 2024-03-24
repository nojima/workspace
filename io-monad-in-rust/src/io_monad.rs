use crate::cached::Cached;

pub struct IO<A>(Cached<'static, A>);

impl<A: 'static> IO<A> {
    pub fn pure(a: A) -> IO<A> {
        IO(Cached::new(|| a))
    }

    pub fn map<B>(self, f: impl FnOnce(A) -> B + 'static) -> IO<B> {
        IO(Cached::new(move || f(self.0.take())))
    }

    pub fn apply<B>(self, f: IO<impl FnOnce(A) -> B + 'static>) -> IO<B> {
        IO(Cached::new(move || {
            let f = f.0.take();
            f(self.0.take())
        }))
    }

    pub fn bind<B>(self, f: impl FnOnce(A) -> IO<B> + 'static) -> IO<B> {
        IO(Cached::new(move || {
            let x = f(self.0.take());
            x.0.take()
        }))
    }
}

#[cfg(test)]
mod tests {
    use crate::cached::Cached;

    use super::IO;

    fn put_str_ln(s: String) -> IO<()> {
        IO(Cached::new(move || println!("{s}")))
    }

    #[test]
    fn test() {
        let action1 = IO::pure("hello".to_string());
        let action2 = action1.bind(|s| put_str_ln(s));
        action2.0.take();
    }
}
