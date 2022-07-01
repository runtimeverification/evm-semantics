{
  description = "A flake for the KEVM Semantics";

  inputs = {
    k.url = "github:runtimeverification/k/b7a3996ccfb985fcd9c0de0fc167862aaa55c6f1";
    nixpkgs.follows = "k/nixpkgs";
    flake-utils.follows = "k/flake-utils";
    blockchain-k-plugin.url = "github:runtimeverification/blockchain-k-plugin/8fdc74e3caf254aa3952393dbb0368d2c98c321a";
    blockchain-k-plugin.inputs.flake-utils.follows = "k/flake-utils";
    blockchain-k-plugin.inputs.nixpkgs.follows = "k/nixpkgs";
  };
  outputs = { self, k, nixpkgs, flake-utils, blockchain-k-plugin }:
    let
      buildInputs = pkgs: [
        pkgs.k
        pkgs.llvm-backend
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

      overlay = final: prev: {
        kevm = prev.stdenv.mkDerivation {
          pname = "kevm";
          version = self.rev or "dirty";
          buildInputs = buildInputs prev;

          src = prev.stdenv.mkDerivation {
            name = "kevm-${self.rev or "dirty"}-src";
            src = prev.lib.cleanSource (prev.nix-gitignore.gitignoreSourcePure [
              ./.gitignore
              ".github/"
              "result*"
              "*.nix"
              "deps/*"
            ] ./.);
            dontBuild = true;

            installPhase = ''
              mkdir $out
              cp -rv $src/* $out
              chmod -R u+w $out
              mkdir -p $out/deps/plugin
              cp -rv ${prev.blockchain-k-plugin-src}/* $out/deps/plugin/
            '';
          };

          dontUseCmakeConfigure = true;

          postPatch = ''
            substituteInPlace cmake/node/CMakeLists.txt \
                --replace 'set(K_LIB ''${K_BIN}/../lib)' 'set(K_LIB ${prev.k}/lib)'
          '';

          buildPhase = ''
            make plugin-deps
            make build
          '';
          installPhase = ''
            mkdir -p $out
            mv .build/usr/* $out/
          '';
        };

      };
    in flake-utils.lib.eachSystem [
      "x86_64-linux"
      "x86_64-darwin"
      "aarch64-linux"
      "aarch64-darwin"
    ] (system: let
          pkgs = import nixpkgs {
        inherit system;
        overlays = [
          (final: prev: { llvm-backend-release = false; })
          k.overlay
          blockchain-k-plugin.overlay
          overlay
        ];
      }; in {
      defaultPackage = pkgs.kevm;

      devShell = pkgs.mkShell { buildInputs = buildInputs pkgs; };

    }) // {
      overlay = nixpkgs.lib.composeManyExtensions [
        k.overlay
        blockchain-k-plugin.overlay
        overlay
      ];
    };
}
