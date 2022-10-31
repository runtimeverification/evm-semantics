{
  description = "A flake for the KEVM Semantics";

  inputs = {
    k-framework.url = "github:runtimeverification/k";
    nixpkgs.follows = "k-framework/nixpkgs";
    flake-utils.follows = "k-framework/flake-utils";
    rv-utils.url = "github:runtimeverification/rv-nix-tools";
    poetry2nix.follows = "pyk/poetry2nix";
    blockchain-k-plugin.url =
      "github:runtimeverification/blockchain-k-plugin/8fdc74e3caf254aa3952393dbb0368d2c98c321a";
    blockchain-k-plugin.inputs.flake-utils.follows = "k-framework/flake-utils";
    blockchain-k-plugin.inputs.nixpkgs.follows = "k-framework/nixpkgs";
    ethereum-tests.url =
      "github:ethereum/tests/6401889dec4eee58e808fd178fb2c7f628a3e039";
    ethereum-tests.flake = false;
    ethereum-legacytests.url =
      "github:ethereum/legacytests/d7abc42a7b352a7b44b1f66b58aca54e4af6a9d7";
    ethereum-legacytests.flake = false;
    haskell-backend.follows = "k-framework/haskell-backend";
    pyk.url = "github:runtimeverification/pyk/v0.1.34";
    pyk.inputs.flake-utils.follows = "k-framework/flake-utils";
    pyk.inputs.nixpkgs.follows = "k-framework/nixpkgs";

  };
  outputs = { self, k-framework, haskell-backend, nixpkgs, flake-utils, poetry2nix
    , blockchain-k-plugin, ethereum-tests, ethereum-legacytests, rv-utils, pyk
    }:
    let
      buildInputs = pkgs: k:
        with pkgs;
        [
          k
          llvm-backend
          autoconf
          cmake
          clang
          llvmPackages.llvm
          cryptopp.dev
          gmp
          graphviz
          mpfr
          openssl.dev
          pkg-config
          procps
          protobuf
          python39
          secp256k1
          solc
          time
          virtualenv
        ] ++ lib.optional (!stdenv.isDarwin) elfutils
        ++ lib.optionals stdenv.isDarwin [ automake libtool ];

      overlay = final: prev: {
        kevm = k:
          prev.stdenv.mkDerivation {
            pname = "kevm";
            version = self.rev or "dirty";
            buildInputs = buildInputs final k;
            nativeBuildInputs = [ prev.makeWrapper ];

            src = prev.stdenv.mkDerivation {
              name = "kevm-${self.rev or "dirty"}-src";
              src = prev.lib.cleanSource
                (prev.nix-gitignore.gitignoreSourcePure [
                  ./.gitignore
                  ".github/"
                  "result*"
                  "*.nix"
                  "deps/"
                  "kevm-pyk/"
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

            patches = [ ./package/nix/kevm.patch ];

            postPatch = ''
              substituteInPlace ./cmake/node/CMakeLists.txt \
                --replace 'set(K_LIB ''${K_BIN}/../lib)' 'set(K_LIB ${k}/lib)'
              substituteInPlace ./bin/kevm \
                --replace 'execute python3 -m kevm_pyk' 'execute ${final.kevm-pyk}/bin/kevm-pyk'
            '';

            buildFlags =
              prev.lib.optional (prev.stdenv.isAarch64 && prev.stdenv.isDarwin)
              "APPLE_SILICON=true";
            enableParallelBuilding = true;

            preBuild = ''
              make plugin-deps
            '';

            installPhase = ''
              mkdir -p $out
              mv .build/usr/* $out/
              wrapProgram $out/bin/kevm --prefix PATH : ${
                prev.lib.makeBinPath [ final.solc prev.which k ]
              }
              ln -s ${k} $out/lib/kevm/kframework
            '';
          };

        kevm-test = k:
          prev.stdenv.mkDerivation {
            pname = "kevm-test";
            version = self.rev or "dirty";

            src = (final.kevm k).src;

            enableParallelBuilding = true;

            buildInputs = [ (final.kevm k) prev.which prev.git ];

            buildPhase = ''
              mkdir -p tests/ethereum-tests/LegacyTests
              cp -rv ${ethereum-tests}/* tests/ethereum-tests/
              cp -rv ${ethereum-legacytests}/* tests/ethereum-tests/LegacyTests/
              chmod -R u+w tests
              APPLE_SILICON=${
                if prev.stdenv.isAarch64 && prev.stdenv.isDarwin then
                  "true"
                else
                  "false"
              } NIX=true package/test-package.sh
            '';

            installPhase = ''
              touch $out
            '';
          };

        kevm-pyk = prev.poetry2nix.mkPoetryApplication {
          python = prev.python39;
          projectDir = ./kevm-pyk;
          overrides = prev.poetry2nix.overrides.withDefaults
            (finalPython: prevPython: { pyk = prev.pyk; });
          groups = [];
          # We remove `"dev"` from `checkGroups`, so that poetry2nix does not try to resolve dev dependencies.
          checkGroups = [];
        };

      };
    in flake-utils.lib.eachSystem [
      "x86_64-linux"
      "x86_64-darwin"
      "aarch64-linux"
      "aarch64-darwin"
    ] (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            (final: prev: { llvm-backend-release = false; })
            k-framework.overlay
            blockchain-k-plugin.overlay
            poetry2nix.overlay
            pyk.overlay
            overlay
          ];
        };
        kevm = pkgs.kevm k-framework.packages.${system}.k;
      in {
        packages.default = kevm;
        devShell = pkgs.mkShell {
          buildInputs = buildInputs pkgs k-framework.packages.${system}.k;
        };

        apps = {
          compare-profiles = flake-utils.lib.mkApp {
            drv = pkgs.stdenv.mkDerivation {
              name = "compare-profiles";
              src = ./package/nix;
              installPhase = ''
                mkdir -p $out/bin
                cp profile.py $out/bin/compare-profiles
              '';
            };
          };
        };

        packages = {
          inherit (pkgs) kevm-pyk;
          inherit kevm;
          kevm-test = pkgs.kevm-test k-framework.packages.${system}.k;

          profile = pkgs.callPackage ./package/nix/profile.nix {
            inherit kevm;
            kore-exec = haskell-backend.packages.${system}."kore:exe:kore-exec";
            src = pkgs.lib.cleanSource (pkgs.nix-gitignore.gitignoreSourcePure [
              ./.gitignore
              ".github/"
              "result*"
              "*.nix"
              "deps/"
              "kevm-pyk/"
            ] ./.);
          };

          check-submodules = rv-utils.lib.check-submodules pkgs {
            inherit k-framework blockchain-k-plugin ethereum-tests
              ethereum-legacytests;
          };

          update-from-submodules =
            rv-utils.lib.update-from-submodules pkgs ./flake.lock {
              k-framework.submodule = "deps/k";
              blockchain-k-plugin.submodule = "deps/plugin";
              ethereum-tests.submodule = "tests/ethereum-tests";
              ethereum-legacytests.submodule =
                "tests/ethereum-tests/LegacyTests";
            };
        };
      }) // {
        overlays.default = nixpkgs.lib.composeManyExtensions [
          k-framework.overlay
          blockchain-k-plugin.overlay
          overlay
        ];
      };
}
