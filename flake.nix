{
  description = "A flake for the KEVM Semantics";

  inputs = {
    k-framework.url = "github:runtimeverification/k/v7.1.218";
    nixpkgs.follows = "k-framework/nixpkgs";
    flake-utils.follows = "k-framework/flake-utils";
    rv-utils.follows = "k-framework/rv-utils";
    poetry2nix.follows = "k-framework/poetry2nix";
    blockchain-k-plugin = {
      url =
        "github:runtimeverification/blockchain-k-plugin/651a2db5afc1789c89553f9113c1afa39e391e35";
      inputs.flake-utils.follows = "k-framework/flake-utils";
      inputs.nixpkgs.follows = "k-framework/nixpkgs";
    };
    haskell-backend.follows = "k-framework/haskell-backend";
  };
  outputs = { self, k-framework, haskell-backend, nixpkgs, flake-utils
    , blockchain-k-plugin, rv-utils, ... }@inputs:
    let
      nixLibs = pkgs:
        with pkgs;
        "-I${openssl.dev}/include -L${openssl.out}/lib -I${secp256k1}/include -L${secp256k1}/lib";
      buildInputs = pkgs:
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
          python310
          time
          secp256k1
        ] ++ lib.optional (!stdenv.isDarwin) elfutils;

      overlay = final: prev:
        let
          poetry2nix =
            inputs.poetry2nix.lib.mkPoetry2Nix { pkgs = prev; };
        in {
          kevm = prev.stdenv.mkDerivation {
            pname = "kevm";
            version = self.rev or "dirty";
            buildInputs = buildInputs final ++ [ final.kevm-pyk ];
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
                cp -r $src/* $out
                chmod -R u+w $out
                mkdir -p $out/deps/plugin
                cp -r ${prev.blockchain-k-plugin-src}/* $out/deps/plugin/
              '';
            };

            dontUseCmakeConfigure = true;

            enableParallelBuilding = true;

            buildPhase = ''
              XDG_CACHE_HOME=$(pwd) NIX_LIBS="${nixLibs prev}" ${
                prev.lib.optionalString
                (prev.stdenv.isAarch64 && prev.stdenv.isDarwin)
                "APPLE_SILICON=true"
              } kdist -v build -j4
            '';

            installPhase = ''
              mkdir -p $out
              cp -r ./kdist-*/* $out/
              mkdir -p $out/bin
              makeWrapper ${final.kevm-pyk}/bin/kevm $out/bin/kevm --prefix PATH : ${
                prev.lib.makeBinPath [
                  prev.which
                  k-framework.packages.${prev.system}.k
                ]
              } --set NIX_LIBS "${nixLibs prev}" --set KDIST_DIR $out
            '';
          };

          kevm-test = prev.stdenv.mkDerivation {
            pname = "kevm-test";
            version = self.rev or "dirty";

            src = final.kevm.src;

            enableParallelBuilding = true;

            buildInputs = [ final.kevm prev.which prev.git ];

            buildPhase = ''
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

          kevm-pyk = poetry2nix.mkPoetryApplication {
            python = prev.python310;
            projectDir = ./kevm-pyk;
            overrides = poetry2nix.overrides.withDefaults
              (finalPython: prevPython: {
                kframework = prev.pyk-python310;
              });
            groups = [ ];
            # We remove `"dev"` from `checkGroups`, so that poetry2nix does not try to resolve dev dependencies.
            checkGroups = [ ];
            postInstall = ''
              mkdir -p $out/${prev.python310.sitePackages}/kevm_pyk/kproj/plugin
              cp -r ${prev.blockchain-k-plugin-src}/* $out/${prev.python310.sitePackages}/kevm_pyk/kproj/plugin/
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
            overlay
          ];
        };
        kevm = pkgs.kevm;
      in {
        packages.default = kevm;
        devShell = pkgs.mkShell {
          buildInputs = buildInputs pkgs ++ [ pkgs.poetry-nixpkgs pkgs.which ];

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
          kevm-test = pkgs.kevm-test;

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
            inherit k-framework blockchain-k-plugin;
          };

          update-from-submodules =
            rv-utils.lib.update-from-submodules pkgs ./flake.lock {
              blockchain-k-plugin.submodule = "deps/plugin";
            };
        };
      }) // {
        overlays.default = nixpkgs.lib.composeManyExtensions [
          blockchain-k-plugin.overlay
          overlay
        ];
      };
}
