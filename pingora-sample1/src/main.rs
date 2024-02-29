use async_trait::async_trait;
use log::info;
use pingora::lb::discovery::ServiceDiscovery;
use pingora::lb::{Backend, Backends};
use pingora::prelude::*;
use pingora::protocols::l4::socket::SocketAddr;
use std::collections::{BTreeSet, HashMap};
use std::io;
use std::sync::Arc;
use std::time::Duration;

pub struct Discovery {}

#[async_trait]
impl ServiceDiscovery for Discovery {
    async fn discover(&self) -> Result<(BTreeSet<Backend>, HashMap<u64, bool>)> {
        let backend_addrs = ["127.0.0.1:8000", "127.0.0.1:8001", "127.0.0.1:8002"];
        let backends = backend_addrs
            .into_iter()
            .map(|s| {
                let addr: SocketAddr = s.parse()?;
                Ok(Backend { addr, weight: 1 })
            })
            .collect::<Result<_>>()?;
        Ok((backends, HashMap::new()))
    }
}

pub struct LB {
    load_balancer: Arc<LoadBalancer<RoundRobin>>,
}

#[async_trait]
impl ProxyHttp for LB {
    type CTX = ();
    fn new_ctx(&self) -> () {
        ()
    }

    async fn upstream_peer(&self, session: &mut Session, _ctx: &mut ()) -> Result<Box<HttpPeer>> {
        let host = session
            .get_header(http::header::HOST)
            .map(|v| String::from_utf8_lossy(v.as_bytes()))
            .ok_or_else(|| Error::explain(HTTPStatus(400), "no host header"))?;
        info!("Host = {host}");

        let upstream = self
            .load_balancer
            .select(b"", 256)
            .ok_or_else(|| Error::explain(HTTPStatus(502), "no upstream available"))?;

        let peer = Box::new(HttpPeer::new(upstream, false, String::new()));
        Ok(peer)
    }
}

/*
fn get_upstream_addr(host: &str) -> Result<String> {
    // parse host header
    static PATTERN: Lazy<Regex> = Lazy::new(|| Regex::new(r"^([a-zA-Z0-9-]+)[.]").unwrap());
    let Some(caps) = PATTERN.captures(host) else {
        return Err(Error::explain(HTTPStatus(400), "invalid host name"));
    };
    let first_label = &caps[1];

    // open file
    let filename = "upstreams/".to_string() + first_label;
    let mut file = match File::open(filename) {
        Ok(f) => Ok(f),
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            Err(Error::explain(HTTPStatus(404), "upstream not found"))
        }
        Err(e) => Err(Error::explain(
            HTTPStatus(500),
            format!("failed to open upstream file: {e}"),
        )),
    }?;

    // read the upstream address from the file
    let mut contents = String::new();
    file.read_to_string(&mut contents)
        .map_err(|e| Error::explain(HTTPStatus(500), format!("internal server error: {e}")))?;
    Ok(contents.trim().to_string())
}
*/

fn main() -> io::Result<()> {
    env_logger::init();

    let mut my_server = Server::new(Some(Opt::default())).unwrap();
    my_server.bootstrap();

    let backends = Backends::new(Box::new(Discovery {}));
    let mut load_balancer = LoadBalancer::from_backends(backends);
    load_balancer.update_frequency = Some(Duration::from_secs(1));
    let background = background_service("service discovery", load_balancer);

    let mut lb = http_proxy_service(
        &my_server.configuration,
        LB {
            load_balancer: background.task(),
        },
    );
    lb.add_tcp("0.0.0.0:6188");

    my_server.add_service(background);
    my_server.add_service(lb);
    my_server.run_forever();
    Ok(())
}
