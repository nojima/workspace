import { useState } from 'react'
import { Container, PasswordInput, TextInput } from '@mantine/core';
import { SHA256_init, SHA256_write, SHA256_finalize, HMAC_SHA256_init, HMAC_SHA256_write, HMAC_SHA256_finalize } from './jssha256';
import './App.css'

function hashToAscii(hash) {
  const CHR_0 = '0'.charCodeAt(0);
  const CHR_A = 'A'.charCodeAt(0);
  const CHR_a = 'a'.charCodeAt(0);

  var result = [];
  for (var i = 0; i < 16; ++i) {
    var n = (hash[i*2] | (hash[i*2+1] << 8)) % 62;
    var code = n < 10 ? CHR_0 + n
             : n < 36 ? CHR_A + n - 10
             :          CHR_a + n - 36
    result.push(String.fromCharCode(code));
  }
  return result.join('');
}

function generateCheckSum(secret) {
  const CHECKSUM_SALT = 'q1RDBvsewQEOBSYv3IzBJ9GRvSoUPqHYh0o87HNrfQuqiOD0MWQZc_RiLwAIhmb2';
  let state = SHA256_init();
  SHA256_write(state, CHECKSUM_SALT + secret);
  return hashToAscii(SHA256_finalize(state)).substr(0, 2);
}

function generatePassword(secret, domain) {
  let state = HMAC_SHA256_init(secret);
  HMAC_SHA256_write(state, domain);
  return hashToAscii(HMAC_SHA256_finalize(state));
}

function App() {
  const reducer = null;
  const [state, setState] = useState({});
  const dispatch = (message) => {
    const [nextState, nextCommand] = reducer(message);
    setState(nextState);
    if (nextCommand != null) {
    }
  };

  const [secret, setSecret] = useState("");
  const [domain, setDomain] = useState("");

  const checksum = generateCheckSum(secret);
  const password = generatePassword(secret, domain);

  return (
    <Container>
      <h1>Domain Password Generator</h1>

      <div className="input-secret">
        <PasswordInput
          label="Secret"
          description={"checksum: " + checksum}
          id="secret"
          width="40"
          autoFocus={true}
          value={secret}
          onChange={e => setSecret(e.currentTarget.value)}
        />
      </div>

      <div className="input-domain">
        <TextInput
          label="Domain"
          id="domain"
          type="url"
          width="40"
          value={domain}
          onChange={e => setDomain(e.currentTarget.value)}
        />
      </div>

      <div className="output-password">
        <TextInput
          variant="filled"
          label="Domain Password"
          id="password"
          type="text"
          width="40"
          readOnly={true}
          value={password}
        />
      </div>
    </Container>
  );
}

export default App
