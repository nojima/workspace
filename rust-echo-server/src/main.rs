use std::io::{self, BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::thread;

const MAX_READ_SIZE: u64 = 1024 * 1024;

fn handle_client(client: TcpStream) -> io::Result<()> {
    let mut reader = BufReader::new(&client);
    let mut buffer = String::new();

    loop {
        // read
        buffer.clear();
        let n = (&mut reader).take(MAX_READ_SIZE).read_line(&mut buffer)?;
        if n == 0 {
            return Ok(());
        }

        // write
        (&client).write_all(buffer.as_bytes())?;
    }
}

fn main() -> io::Result<()> {
    let listener = TcpListener::bind("[::]:3000")?;
    eprintln!("server started on port 3000");

    for stream in listener.incoming() {
        let stream = match stream {
            Ok(x) => x,
            Err(e) => {
                eprintln!("failed to accept connection: {e}");
                continue;
            }
        };

        thread::spawn(move || {
            eprintln!("connection accepted");
            if let Err(e) = handle_client(stream) {
                eprintln!("failed to handle client: {e}");
                return;
            }
            eprintln!("connection done");
        });
    }
    Ok(())
}
