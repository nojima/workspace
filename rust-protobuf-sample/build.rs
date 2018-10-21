extern crate protoc_rust;

use protoc_rust::Customize;
use std::error::Error;

fn main() -> Result<(), Box<Error>> {
    let proto_files = vec!["src/person.proto"];

    protoc_rust::run(protoc_rust::Args {
        input: &proto_files[..],
        out_dir: "src/protos",
        includes: &[],
        customize: Customize {
            ..Default::default()
        },
    })?;
    Ok(())
}
