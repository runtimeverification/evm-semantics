{
  description = "A flake for the KEVM Semantics";

  inputs = {
    rv-nix-tools.url = "github:runtimeverification/rv-nix-tools/854d4f05ea78547d46e807b414faad64cea10ae4";
    nixpkgs.follows = "rv-nix-tools/nixpkgs";

    k-framework.url = "github:runtimeverification/k/v7.1.275";
    k-framework.inputs.nixpkgs.follows = "nixpkgs";
    flake-utils.follows = "k-framework/flake-utils";
    poetry2nix = {
      url = "github:nix-community/poetry2nix/2024.9.219347";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    blockchain-k-plugin = {
      url =
        "github:runtimeverification/blockchain-k-plugin/f159396d0f16b88c86c557c47f7ae36ffc59dc53";
      inputs.flake-utils.follows = "k-framework/flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    haskell-backend.follows = "k-framework/haskell-backend";
  };
  outputs = { self, k-framework, haskell-backend, nixpkgs, flake-utils
    , blockchain-k-plugin, rv-nix-tools, ... }@inputs:
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
                  "kevm-pyk/"
                  # do not include submodule directories that might be initialized empty or non-existent
                  "/deps/"
                  "/tests/ethereum-tests"
                  "/web/k-web-theme"
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
            projectDir = prev.lib.cleanSource (
              prev.nix-gitignore.gitignoreSourcePure [
                ./.gitignore
                # do not include submodule directories that might be initialized empty or non-existent
                "/src/kevm_pyk/kproj/plugin"
              ] ./kevm-pyk/.
            );
            overrides = poetry2nix.overrides.withDefaults (finalPython: prevPython: {
              click = prevPython.click.overridePythonAttrs (
                old: {
                  buildInputs = (old.buildInputs or [ ]) ++ [ finalPython.flit-core ];
                  patches = (old.patches or [ ]) ++ [
                    ./nix/resources/click-pyproject.toml.patch
                  ];
                }
              );
              typing-extensions = prevPython.typing-extensions.overridePythonAttrs (
                old: {
                  patches = (old.patches or [ ]) ++ [
                    ./nix/resources/typing-extensions-pyproject.toml.patch
                  ];
                }
              );
              types-python-dateutil = prevPython.types-python-dateutil.overridePythonAttrs (
                old: {
                  patches = (old.patches or [ ]) ++ [
                    ./nix/resources/types-python-dateutil-pyproject.toml.patch
                  ];
                }
              );
              zipp = prevPython.zipp.overridePythonAttrs (
                old: {
                  patches = (old.patches or [ ]) ++ [
                    ./nix/resources/zipp-pyproject.toml.patch
                  ];
                }
              );
              urllib3 = prevPython.urllib3.overridePythonAttrs (
                old: {
                  buildInputs = (old.buildInputs or [ ]) ++ [ finalPython.hatch-vcs ];
                  patches = (old.patches or [ ]) ++ [
                    ./nix/resources/urllib3-pyproject.toml.patch
                  ];
                }
              );
              attrs = prevPython.attrs.overridePythonAttrs (
                old: {
                  patches = (old.patches or [ ]) ++ [
                    ./nix/resources/attrs-pyproject.toml.patch
                  ];
                }
              );
              hypothesis = prevPython.hypothesis.overridePythonAttrs (
                old: {
                  patches = (old.patches or [ ]) ++ [
                    ./nix/resources/hypothesis-pyproject.toml.patch
                  ];
                }
              );
              graphviz = prevPython.graphviz.overridePythonAttrs (
                old: {
                  patches = (old.patches or [ ]) ++ [
                    ./nix/resources/graphviz-pyproject.toml.patch
                  ];
                }
              );
              kframework = prevPython.kframework.overridePythonAttrs (
                old: {
                  buildInputs = (old.buildInputs or [ ]) ++ [ finalPython.hatchling ];
                }
              );
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
              "kevm-pyk/"
              # do not include submodule directories that might be initialized empty or non-existent
              "/deps/"
              "/tests/ethereum-tests"
              "/web/k-web-theme"
            ] ./.);
          };

          check-submodules = rv-nix-tools.lib.check-submodules pkgs {
            inherit k-framework blockchain-k-plugin;
          };

          update-from-submodules =
            rv-nix-tools.lib.update-from-submodules pkgs ./flake.lock {
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
