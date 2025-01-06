{
  description = "yrmcds is a memcached compatible KVS";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
  };

  # outputs のスキーマは以下のページが詳しい:
  # https://zenn.dev/asa1984/books/nix-hands-on/viewer/ch01-05-flake-outputs
  outputs = { nixpkgs, ... }:
    let
      # とりあえず x86_64-linux のみを対象としてビルドすることにする。
      system = "x86_64-linux";
      # nixpkgs という全部入りのパッケージリポジトリから x86_64 のパッケージ集合
      # だけを抜き出してきて "pkgs" 変数に束縛する（一般的なお作法らしい）。
      pkgs = nixpkgs.legacyPackages.${system};
      # yrmcds の derivation を定義する。
      # pkgs.stdenv はパッケージをビルドするための標準的なパッケージを集めた環境であり、
      # coreutils, bash, gcc, make などが入っている。
      yrmcds = pkgs.stdenv.mkDerivation {
        pname = "yrmcds";
        version = "1.1.12";
        # ソースコードを GitHub から取得する。
        # ビルドを reproducible にするためにハッシュを必ず指定する必要がある。
        src = pkgs.fetchFromGitHub {
          owner = "cybozu";
          repo = "yrmcds";
          rev = "v1.1.12";
          hash = "sha256-zoQRqun8OFkkOU+4brTXJtbr/kvtPg22r+i2yoSnWD0=";
        };
        # ビルドに必要な入力を定義する。
        # 型は list of derivation。
        # パッケージ名は https://search.nixos.org/ で調べるとよいらしい。
        nativeBuildInputs = [ pkgs.gperftools ];
        # ビルドするためのシェルコマンドを定義する。
        # このコマンドは上で指定した src を作業ディレクトリとして実行される。
        buildPhase = ''
          make
        '';
        # $out という環境変数の指すディレクトリに生成物をコピーするためのコマンドを記述する。
        # $out の中身がこのビルドのアウトプットであるとみなされる。
        installPhase = ''
          mkdir -p $out/bin
          cp ./yrmcdsd $out/bin/yrmcdsd
        '';
        # メタデータ
        meta = {
          # nix run したときに実行されるファイル名はこれで決まる模様。
          mainProgram = "yrmcdsd";
          # 説明。longDescription という属性もある。
          description = "A memcached compatible KVS";
          # ライセンス。一覧は↓を見るとよい。
          # https://github.com/NixOS/nixpkgs/blob/master/lib/licenses.nix
          license = pkgs.lib.licenses.bsd2;
        };
      };
    in
    {
      # 定義した derivation を `packages.<プラットフォーム>.<パッケージ名>` という名前で出力すると
      # `nix build <flake-url>#<パッケージ名>` でビルドできるようになる。
      # また、 `packages.<プラットフォーム>.default` という名前で出力すると
      # `nix build <flake-url>` でビルドできる。
      packages.${system} = {
        inherit yrmcds;
        default = yrmcds;
      };

      # `nix develop <flake-url>` で起動するシェル。
      # これがなくてもビルドには支障ないが、用意しておくとアドホックにコマンドを試せて便利。
      devShells.${system}.default = pkgs.mkShell {
        packages = [ pkgs.gperftools ];
      };
    };
}
