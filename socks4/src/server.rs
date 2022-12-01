use std::io::{self, BufRead, BufReader, Read, Write};
use std::net::{Ipv4Addr, SocketAddr, TcpStream};
use std::thread;
use std::time::Duration;

const MAX_IDENT_LEN: u64 = 256;

const CODE_SUCCESS: u8 = 90;
const CODE_FAILURE: u8 = 91;

struct Handler {
    client_read_timeout: Duration,
    client_write_timeout: Duration,
    upstream_connect_timeout: Duration,
    upstream_read_timeout: Duration,
    upstream_write_timeout: Duration,
}

impl Handler {
    fn handle(&self, mut client: TcpStream) -> io::Result<()> {
        client.set_read_timeout(Some(self.client_read_timeout))?;
        client.set_write_timeout(Some(self.client_write_timeout))?;
        let mut client_reader = BufReader::new(client.try_clone()?);

        let upstream_addr = self.read_request(&mut client_reader)?;

        // TODO: authorization

        let upstream = match self.connect_to_upstream(upstream_addr) {
            Ok(u) => u,
            Err(e) => {
                // TODO: log e
                self.send_response(&mut client, CODE_FAILURE)?;
                return Ok(());
            }
        };
        let upstream_reader = upstream.try_clone()?;

        self.send_response(&mut client, CODE_SUCCESS)?;

        self.do_proxy(client_reader, client, upstream_reader, upstream)
    }

    fn read_request(&self, client_reader: &mut impl BufRead) -> io::Result<SocketAddr> {
        let mut buf: [u8; 1 + 1 + 2 + 4] = Default::default();
        client_reader.read_exact(&mut buf)?;

        let version = buf[0];
        // TODO: check version

        let command = buf[1];
        // TODO: check command

        let dst_port = u16::from_be_bytes([buf[2], buf[3]]);
        let dst_addr = Ipv4Addr::new(buf[4], buf[5], buf[6], buf[7]);

        let mut ident = vec![];
        client_reader
            .take(MAX_IDENT_LEN)
            .read_until(0, &mut ident)?;

        Ok(SocketAddr::from((dst_addr, dst_port)))
    }

    fn connect_to_upstream(&self, addr: SocketAddr) -> io::Result<TcpStream> {
        let upstream = TcpStream::connect_timeout(&addr, self.upstream_connect_timeout)?;
        upstream.set_read_timeout(Some(self.upstream_read_timeout))?;
        upstream.set_write_timeout(Some(self.upstream_write_timeout))?;
        Ok(upstream)
    }

    fn send_response(&self, client: &mut impl Write, code: u8) -> io::Result<()> {
        let resp = [
            0,    // VN
            code, // CD
            0, 0, // DSTPORT
            0, 0, 0, 0, // DSTIP
        ];
        client.write_all(&resp)
    }

    fn do_proxy(
        &self,
        mut client_reader: impl Read + Send,
        mut client_writer: impl Write + Send,
        mut upstream_reader: impl Read + Send,
        mut upstream_writer: impl Write + Send,
    ) -> io::Result<()> {
        thread::scope(move |scope| {
            let t1 = scope.spawn(move || io::copy(&mut client_reader, &mut upstream_writer));
            let r2 = io::copy(&mut upstream_reader, &mut client_writer);
            let r1 = t1.join().unwrap();
            r1.and(r2)
        })?;
        Ok(())
    }
}
