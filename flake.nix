{
  description = "A flake for the KEVM Semantics";

  inputs = {
    k.url = "github:runtimeverification/k/96856a68512a89f649ea3d307e2b708ef1e7354c";
    nixpkgs.follows = "k/nixpkgs";
    flake-utils.follows = "k/flake-utils";
  };
  outputs = { self, k, nixpkgs, flake-utils }: flake-utils.lib.eachSystem [
      "x86_64-linux"
      "x86_64-darwin"
      "aarch64-linux"
      "aarch64-darwin"
    ] (system: {

    devShell =
      let pkgs = import nixpkgs { inherit system; overlays = [(final: prev: { llvm-backend-release = false; }) k.overlays.llvm-backend]; };
      in
      pkgs.mkShell {
        buildInputs = [
          k.defaultPackage.${system}
          # kframework.z3
          pkgs.llvm-backend
          # haskell-backend
          pkgs.autoconf
          pkgs.cmake
          pkgs.clang
          pkgs.llvmPackages.llvm
          pkgs.cryptopp.dev
          pkgs.elfutils
          pkgs.gmp
          pkgs.graphviz
          pkgs.mpfr
          pkgs.openssl.dev
          pkgs.pkg-config
          pkgs.procps
          pkgs.protobuf
          pkgs.python38
          pkgs.secp256k1
          pkgs.solc
          pkgs.time
          pkgs.virtualenv
        ];
      };

  });
}