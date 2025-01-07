{ makeRustPlatform, rust-bin, openssl, pkg-config }:
let
  toolchain = rust-bin.stable.latest.default;
  rustPlatform = makeRustPlatform {
    cargo = toolchain;
    rustc = toolchain;
  };
  cargoTOML = builtins.fromTOML (builtins.readFile ../Cargo.toml);
in
rustPlatform.buildRustPackage {
  pname = cargoTOML.package.name;
  version = cargoTOML.package.version;

  buildInputs = [ openssl ];
  nativeBuildInputs = [ pkg-config ];

  src = ../.;
  cargoLock.lockFile = ../Cargo.lock;
}
