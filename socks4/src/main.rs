use std::net::TcpListener;
use std::thread::Scope;
use std::{io, thread};

mod server;

fn main_loop<'handler, 'scope, 'env>(
    listener: TcpListener,
    handler: &'handler server::Handler,
    scope: &'scope Scope<'scope, 'env>,
) -> io::Result<()>
where
    'handler: 'scope,
{
    eprintln!("Server start");
    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                scope.spawn(move || {
                    if let Err(e) = handler.handle(stream) {
                        eprintln!("ERROR: {e}");
                    }
                });
            }
            Err(e) => {
                eprintln!("ERROR: {e}");
            }
        }
    }
    Ok(())
}

fn main() -> io::Result<()> {
    let listener = TcpListener::bind("[::]:1080")?;
    let handler = server::Handler::default();
    let handler_ref = &handler;
    thread::scope(move |scope| main_loop(listener, handler_ref, scope))
}
