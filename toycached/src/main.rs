use std::collections::HashMap;
use std::io::{self, BufRead, BufReader, Read, Write, IoSlice};
use std::net::{TcpListener, TcpStream};
use std::thread;

const MAX_READ_SIZE: u64 = 1024;

fn process_command(
    db: &mut HashMap<String, Vec<u8>>,
    mut reader: impl BufRead,
    mut writer: impl Write,
    buffer: &mut String,
) -> anyhow::Result<bool> {
    buffer.clear();
    let n = (&mut reader).take(MAX_READ_SIZE).read_line(buffer)?;
    if n == 0 {
        return Ok(true);
    }

    let mut iter = buffer.split_ascii_whitespace();

    let Some(cmd) = iter.next() else {
        anyhow::bail!("parse error");
    };

    match cmd {
        "get" => {
            let Some(key) = iter.next() else {
                anyhow::bail!("missing argument: `key`");
            };
            match db.get(key) {
                Some(data) => {
                    let header = format!("VALUE {} {} {}\r\n", key, 0, data.len());
                    let resp = [
                        header.as_bytes(),
                        &data[..],
                        b"\r\n",
                        b"END\r\n",
                    ].concat();
                    writer.write_all(&resp)?;
                }
                None => {
                    writer.write_all(b"END\r\n")?;
                }
            }
        }
        "set" => {
            let Some(key) = iter.next() else {
                anyhow::bail!("missing argument: `key`");
            };
            let Some(flags) = iter.next() else {
                anyhow::bail!("missing argument: `flags`");
            };
            let Ok(_flags) = flags.parse::<u32>() else {
                anyhow::bail!("`flags` must be a 32-bit unsigned integer");
            };
            let Some(exptime) = iter.next() else {
                anyhow::bail!("missing argument: `exptime`");
            };
            let Ok(_exptime) = exptime.parse::<u64>() else {
                anyhow::bail!("`exptime` must be a 64-bit unsigned integer");
            };
            let Some(n_bytes) = iter.next() else {
                anyhow::bail!("missing argument: `bytes`");
            };
            let Ok(n_bytes) = n_bytes.parse::<u32>() else {
                anyhow::bail!("`bytes` must be a 32-bit unsigned integer")
            };
            let _no_reply = iter.next() == Some("no_reply");

            let mut data = vec![0u8; n_bytes as usize];
            reader.read_exact(&mut data)?;

            let mut crlf = [0u8; 2];
            reader.read_exact(&mut crlf)?;
            if crlf != [0x0D, 0x0A] {
                anyhow::bail!("parse error");
            }

            db.insert(key.to_owned(), data);

            writer.write_all(b"STORED\r\n")?;
        }
        _ => {
            anyhow::bail!("unknown command: {cmd}")
        }
    }

    Ok(false)
}

fn handle_client(client: TcpStream) -> anyhow::Result<()> {
    let mut db: HashMap<String, Vec<u8>> = HashMap::new();
    let mut reader = BufReader::new(&client);
    let mut buffer = String::new();

    loop {
        let done = process_command(&mut db, &mut reader, &client, &mut buffer)?;
        if done {
            return Ok(());
        }
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
