{
  description = "A flake for the KEVM Semantics";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/b01f185e4866de7c5b5a82f833ca9ea3c3f72fc4";
    k-framework.url = "github:runtimeverification/k/v6.0.150";
    k-framework.inputs.nixpkgs.follows = "nixpkgs";
    #nixpkgs.follows = "k-framework/nixpkgs";
    flake-utils.follows = "k-framework/flake-utils";
    rv-utils.url = "github:runtimeverification/rv-nix-tools";
    poetry2nix.follows = "pyk/poetry2nix";
    blockchain-k-plugin.url = "github:runtimeverification/blockchain-k-plugin/b42e6ede9f6b72cedabc519810416e2994caad45";
    blockchain-k-plugin.inputs.flake-utils.follows = "k-framework/flake-utils";
    blockchain-k-plugin.inputs.nixpkgs.follows = "k-framework/nixpkgs";
    ethereum-tests.url = "github:ethereum/tests/6401889dec4eee58e808fd178fb2c7f628a3e039";
    ethereum-tests.flake = false;
    ethereum-legacytests.url = "github:ethereum/legacytests/d7abc42a7b352a7b44b1f66b58aca54e4af6a9d7";
    ethereum-legacytests.flake = false;
    haskell-backend.follows = "k-framework/haskell-backend";
    pyk.url = "github:runtimeverification/pyk/v0.1.472";
    pyk.inputs.flake-utils.follows = "k-framework/flake-utils";
    pyk.inputs.nixpkgs.follows = "k-framework/nixpkgs";
    foundry.url = "github:shazow/foundry.nix/monthly"; # Use monthly branch for permanent releases
    solc = {
      url = "github:hellwolf/solc.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };
  outputs = { self, k-framework, haskell-backend, nixpkgs, flake-utils
    , poetry2nix, blockchain-k-plugin, ethereum-tests, ethereum-legacytests
    , rv-utils, pyk, foundry, solc }:
    let
      nixLibs = pkgs:
        with pkgs;
        "-I${procps}/include -L${procps}/lib -I${openssl.dev}/include -L${openssl.out}/lib";
      buildInputs = pkgs: k:
        with pkgs;
        [
          k
          llvm-backend
          autoconf
          automake
          cmake
          clang
          llvmPackages.llvm
          fmt
          libtool
          mpfr
          openssl.dev
          pkg-config
          procps
          python310
          (solc.mkDefault pkgs solc_0_8_13)
          time
        ] ++ lib.optional (!stdenv.isDarwin) elfutils;

      overlay = final: prev: {
        kevm = k:
          prev.stdenv.mkDerivation {
            pname = "kevm";
            version = self.rev or "dirty";
            buildInputs = buildInputs final k ++ [ final.kevm-pyk ];
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

            enableParallelBuilding = true;

            buildPhase = ''
              XDG_CACHE_HOME=$(pwd) NIX_LIBS="${nixLibs prev}" ${
                prev.lib.optionalString
                (prev.stdenv.isAarch64 && prev.stdenv.isDarwin)
                "APPLE_SILICON=true"
              } kevm-dist build -j4
            '';

            installPhase = ''
              mkdir -p $out
              cp -r ./evm-semantics-*/* $out/
              mkdir -p $out/bin
              makeWrapper ${final.kevm-pyk}/bin/kevm $out/bin/kevm --prefix PATH : ${
                prev.lib.makeBinPath [ prev.which k ]
              } --set NIX_LIBS "${nixLibs prev}" --set KEVM_DIST_DIR $out
              makeWrapper ${final.kevm-pyk}/bin/kontrolx $out/bin/kontrolx --prefix PATH : ${
                prev.lib.makeBinPath [
                  (solc.mkDefault final final.solc_0_8_13)
                  final.foundry-bin
                  prev.which
                  k
                ]
              } --set NIX_LIBS "${nixLibs prev}" --set KEVM_DIST_DIR $out
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
          python = prev.python310;
          projectDir = ./kevm-pyk;

          postPatch = ''
            substituteInPlace ./src/kontrolx/foundry.py \
              --replace "'forge', 'build'," "'forge', 'build', '--no-auto-detect',"
          '';

          overrides = prev.poetry2nix.overrides.withDefaults
            (finalPython: prevPython: {
              pyk = prev.pyk-python310;
              xdg-base-dirs = prevPython.xdg-base-dirs.overridePythonAttrs
                (old: {
                  propagatedBuildInputs = (old.propagatedBuildInputs or [ ])
                    ++ [ finalPython.poetry ];
                });
            });
          groups = [ ];
          # We remove `"dev"` from `checkGroups`, so that poetry2nix does not try to resolve dev dependencies.
          checkGroups = [ ];

          postInstall = ''
            mkdir -p $out/${prev.python310.sitePackages}/kevm_pyk/kproj/plugin
            cp -rv ${prev.blockchain-k-plugin-src}/* $out/${prev.python310.sitePackages}/kevm_pyk/kproj/plugin/
          '';
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
            (final: prev: {
              llvm-backend-release = false;
              poetry-nixpkgs = prev.poetry;
            })
            k-framework.overlay
            blockchain-k-plugin.overlay
            poetry2nix.overlay
            pyk.overlay
            foundry.overlay
            solc.overlay
            overlay
          ];
        };
        kevm = pkgs.kevm k-framework.packages.${system}.k;
      in {
        packages.default = kevm;
        devShell = pkgs.mkShell {
          buildInputs = buildInputs pkgs k-framework.packages.${system}.k
            ++ [ pkgs.poetry-nixpkgs pkgs.foundry-bin ];

          shellHook = ''
            export NIX_LIBS="${nixLibs pkgs}"
            ${pkgs.lib.strings.optionalString
            (pkgs.stdenv.isAarch64 && pkgs.stdenv.isDarwin)
            "export APPLE_SILICON=true"}
          '';
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
              blockchain-k-plugin.submodule = "deps/plugin";
              ethereum-tests.submodule = "tests/ethereum-tests";
              ethereum-legacytests.submodule =
                "tests/ethereum-tests/LegacyTests";
            };
        };
      }) // {
        overlays.default = nixpkgs.lib.composeManyExtensions [
          blockchain-k-plugin.overlay
          overlay
        ];
      };
}
