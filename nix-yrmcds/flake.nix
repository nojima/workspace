{
  description = "yrmcds is a memcached compatible KVS";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        yrmcds = pkgs.stdenv.mkDerivation {
          pname = "yrmcds";
          version = "1.1.12";
          src = pkgs.fetchFromGitHub {
            owner = "cybozu";
            repo = "yrmcds";
            rev = "v1.1.12";
            hash = "sha256-zoQRqun8OFkkOU+4brTXJtbr/kvtPg22r+i2yoSnWD0=";
          };
          nativeBuildInputs = [ pkgs.gperftools ];
          buildPhase = ''
            make
          '';
          installPhase = ''
            mkdir -p $out/bin
            cp ./yrmcdsd $out/bin/yrmcdsd
          '';
          meta = {
            mainProgram = "yrmcdsd";
            description = "A memcached compatible KVS";
            license = pkgs.lib.licenses.bsd2;
          };
        };
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [ pkgs.gperftools ];
        };
        packages = {
          inherit yrmcds;
          default = yrmcds;
        };
      }
    );
}
