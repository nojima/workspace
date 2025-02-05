use base64::{prelude::BASE64_STANDARD_NO_PAD, Engine};
use openssl::{
    derive::Deriver,
    pkey::{Id, PKey, Private, Public},
};

struct State {
    private_key: PKey<Private>,
    public_key: PKey<Public>,
}

fn generate_key() -> anyhow::Result<State> {
    let private_key = PKey::generate_x25519()?;
    let public_key = {
        let raw = private_key.raw_public_key()?;
        PKey::public_key_from_raw_bytes(&raw, Id::X25519)?
    };
    Ok(State {
        private_key,
        public_key,
    })
}

fn key_exchange(state: &State, peer_public_key: &PKey<Public>) -> anyhow::Result<Vec<u8>> {
    let mut deriver = Deriver::new(&state.private_key)?;
    deriver.set_peer(peer_public_key)?;
    Ok(deriver.derive_to_vec()?)
}

fn main() -> anyhow::Result<()> {
    let alice = generate_key()?;
    let bob = generate_key()?;

    println!(
        "alice/public_key = {}",
        BASE64_STANDARD_NO_PAD.encode(alice.public_key.public_key_to_der()?)
    );
    println!(
        "  bob/public_key = {}",
        BASE64_STANDARD_NO_PAD.encode(bob.public_key.public_key_to_der()?)
    );

    let alice_secret = key_exchange(&alice, &bob.public_key)?;
    let bob_secret = key_exchange(&bob, &alice.public_key)?;

    println!(
        "alice/shared_secret = {}",
        BASE64_STANDARD_NO_PAD.encode(alice_secret)
    );
    println!(
        "  bob/shared_secret = {}",
        BASE64_STANDARD_NO_PAD.encode(bob_secret)
    );

    Ok(())
}
