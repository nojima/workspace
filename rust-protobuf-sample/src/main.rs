mod protos;

extern crate protobuf;

use protobuf::Message;
use std::error::Error;
use std::fs::File;
use std::io::Read;

use protos::person::Person;

fn write_protobuf(filename: &str) -> Result<(), Box<Error>> {
    let mut person = Person::new();
    person.set_id(42);
    person.set_name("Yusuke Nojima".to_string());

    let mut file = File::create(filename)?;
    person.write_to_writer(&mut file)?;

    Ok(())
}

fn read_protobuf(filename: &str) -> Result<Person, Box<Error>> {
    let mut file = File::open(filename)?;

    let mut buffer = vec![];
    file.read_to_end(&mut buffer)?;

    let mut person = Person::new();
    person.merge_from_bytes(&buffer[..])?;

    Ok(person)
}

fn main() {
    let filename = "/tmp/person.bin";

    write_protobuf(filename).unwrap();

    let person = read_protobuf(filename).unwrap();
    println!("id={}, name='{}'", person.id, person.name);
}
