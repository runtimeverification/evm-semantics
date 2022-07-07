{
  description = "A flake for the KEVM Semantics";

  inputs = {
    k-framework.url = "github:runtimeverification/k/3cf3d2556a5eaf94299b57a1874c451283c249f6";
    nixpkgs.follows = "k-framework/nixpkgs";
    flake-utils.follows = "k-framework/flake-utils";
    pynixify.follows = "k-framework/pynixify";
    blockchain-k-plugin.url =
      "github:runtimeverification/blockchain-k-plugin/8fdc74e3caf254aa3952393dbb0368d2c98c321a";
    blockchain-k-plugin.inputs.flake-utils.follows = "k-framework/flake-utils";
    blockchain-k-plugin.inputs.nixpkgs.follows = "k-framework/nixpkgs";
  };
  outputs =
    { self, k-framework, nixpkgs, flake-utils, pynixify, blockchain-k-plugin }:
    let
      buildInputs = pkgs:
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
          python38
          secp256k1
          solc
          time
          virtualenv
        ] ++ lib.optional (!stdenv.isDarwin) elfutils
        ++ lib.optionals stdenv.isDarwin [ automake libtool ];

      overlay = final: prev:
        let
          pythonOverrides = nixpkgs.lib.composeManyExtensions [
            prev.pythonOverrides
            (import ./kevm_pyk/nix/overlay.nix)
            (finalPython: prevPython: {
              # another hacky thing. we need to modify setup.cfg and remove '@ git+...'
              # after pyk, otherwise pip will try to download pyk from the github repo
              kevm_pyk = prevPython.kevm_pyk.overrideAttrs (_: {
                src = prev.stdenv.mkDerivation {
                  name = "kevm_pyk-${self.rev or "dirty"}-src";
                  src = ./kevm_pyk;
                  dontBuild = true;
                  installPhase = ''
                    mkdir $out
                    cp -rv ./* $out
                    chmod -R u+w $out
                    sed -i "$out/setup.cfg" -e 's/pyk @ git.*/pyk/g'
                  '';
                };
              });
            })
          ];
        in {
          inherit pythonOverrides;
          # solc derivation is broken for darwin M1 in the version of nixpkgs we are on
          # the derivation below is a copy from nixpkgs 22.05
          solc = prev.callPackage ./nix/solc.nix { };

          kevm = prev.stdenv.mkDerivation {
            pname = "kevm";
            version = self.rev or "dirty";
            buildInputs = buildInputs final;

            src = prev.stdenv.mkDerivation {
              name = "kevm-${self.rev or "dirty"}-src";
              src = prev.lib.cleanSource
                (prev.nix-gitignore.gitignoreSourcePure [
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

            prePatch = ''
              substituteInPlace ./cmake/node/CMakeLists.txt \
                  --replace 'set(K_LIB ''${K_BIN}/../lib)' 'set(K_LIB ${prev.k}/lib)'
            '';
            patches = [ ./nix/kevm.patch ];

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
              ln -s ${prev.k} $out/lib/kevm/kframework
            '';
          };

        } // prev.lib.genAttrs [
          "python2"
          "python27"
          "python3"
          "python35"
          "python36"
          "python37"
          "python38"
          "python39"
          "python310"
        ] (python:
          prev.${python}.override { packageOverrides = pythonOverrides; });
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
            overlay
          ];
        };
      in {
        defaultPackage = pkgs.kevm;
        devShell = pkgs.mkShell { buildInputs = buildInputs pkgs; };

        packages = {

          kevm-pyk = pkgs.python38Packages.kevm_pyk;
          # using a specially patched version of pynixify, we can pass a
          # --ignore-packages pyk directive, telling pynixify not to generate a
          # nix expression for the pyk dependency
          update-python = pkgs.writeShellScriptBin "update-python" ''
            #!/bin/sh
            cd kevm_pyk
            ${
              pynixify.packages.${system}.pynixify
            }/bin/pynixify -l kevm_pyk --overlay-only --ignore-packages pyk --output ./nix
          '';
        };
      }) // {
        overlay = nixpkgs.lib.composeManyExtensions [
          k-framework.overlay
          blockchain-k-plugin.overlay
          overlay
        ];
      };
}
