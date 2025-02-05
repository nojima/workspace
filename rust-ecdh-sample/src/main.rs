use base64::prelude::{BASE64_STANDARD_NO_PAD, Engine};
use x25519_dalek::{PublicKey, SharedSecret, StaticSecret};

struct State {
    private_key: StaticSecret,
    public_key: PublicKey,
}

fn generate_key() -> anyhow::Result<State> {
    let private_key = StaticSecret::random();
    let public_key = PublicKey::from(&private_key);
    Ok(State {
        private_key,
        public_key,
    })
}

fn key_exchange(state: &State, peer_public_key: &PublicKey) -> SharedSecret {
    state.private_key.diffie_hellman(peer_public_key)
}

fn main() -> anyhow::Result<()> {
    let alice = generate_key()?;
    let bob = generate_key()?;

    println!(
        "alice/public_key = {}",
        BASE64_STANDARD_NO_PAD.encode(alice.public_key.to_bytes())
    );
    println!(
        "  bob/public_key = {}",
        BASE64_STANDARD_NO_PAD.encode(bob.public_key.to_bytes())
    );

    let alice_secret = key_exchange(&alice, &bob.public_key);
    let bob_secret = key_exchange(&bob, &alice.public_key);

    println!(
        "alice/shared_secret = {}",
        BASE64_STANDARD_NO_PAD.encode(alice_secret.as_bytes())
    );
    println!(
        "  bob/shared_secret = {}",
        BASE64_STANDARD_NO_PAD.encode(bob_secret.as_bytes())
    );

    Ok(())
}
