use anyhow::anyhow;
use base64::{prelude::BASE64_STANDARD_NO_PAD, Engine};
use chacha20poly1305::{
    aead::{Aead, AeadCore, KeyInit, OsRng, Payload},
    ChaCha20Poly1305, Key, Nonce,
};

struct Encrypted {
    nonce: Vec<u8>,
    ciphertext: Vec<u8>,
}

fn encrypt(key: &[u8], plaintext: &[u8], aad: &[u8]) -> anyhow::Result<Encrypted> {
    let cipher = ChaCha20Poly1305::new(Key::from_slice(key));
    let nonce = ChaCha20Poly1305::generate_nonce(&mut OsRng);
    let ciphertext = cipher
        .encrypt(&nonce, Payload { msg: plaintext, aad })
        .map_err(|_| anyhow!("failed to encrypt"))?;
    Ok(Encrypted {
        nonce: nonce.to_vec(),
        ciphertext,
    })
}

fn decrypt(key: &[u8], nonce: &[u8], ciphertext: &[u8], aad: &[u8]) -> anyhow::Result<Vec<u8>> {
    let cipher = ChaCha20Poly1305::new(Key::from_slice(key));
    let nonce = Nonce::from_slice(nonce);
    let plaintext = cipher
        .decrypt(nonce, Payload { msg: ciphertext, aad })
        .map_err(|_| anyhow!("failed to decrypt"))?;
    Ok(plaintext)
}

fn main() -> anyhow::Result<()> {
    let key = ChaCha20Poly1305::generate_key(&mut OsRng);
    let plaintext = b"Hello, World!!";
    let aad = b"123";

    let Encrypted { nonce, ciphertext } = encrypt(&key, plaintext, aad)?;

    println!("nonce = {}", BASE64_STANDARD_NO_PAD.encode(&nonce));
    println!("ciphertext = {}", BASE64_STANDARD_NO_PAD.encode(&ciphertext));

    let decrypted = decrypt(&key, &nonce, &ciphertext, aad)?;

    println!("decrypted = {}", String::from_utf8_lossy(&decrypted));

    Ok(())
}
