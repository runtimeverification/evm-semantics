{
  description = "A flake for the KEVM Semantics";

  inputs = {
    rv-nix-tools.url = "github:runtimeverification/rv-nix-tools/854d4f05ea78547d46e807b414faad64cea10ae4";
    nixpkgs.follows = "rv-nix-tools/nixpkgs";

    k-framework.url = "github:runtimeverification/k/v7.1.280";
    k-framework.inputs.nixpkgs.follows = "nixpkgs";
    flake-utils.follows = "k-framework/flake-utils";
    blockchain-k-plugin = {
      url =
        "github:runtimeverification/blockchain-k-plugin/f159396d0f16b88c86c557c47f7ae36ffc59dc53";
      inputs.flake-utils.follows = "k-framework/flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    haskell-backend.follows = "k-framework/haskell-backend";
    uv2nix.url = "github:pyproject-nix/uv2nix/680e2f8e637bc79b84268949d2f2b2f5e5f1d81c";
    # stale nixpkgs is missing the alias `lib.match` -> `builtins.match`
    # therefore point uv2nix to a patched nixpkgs, which introduces this alias
    # this is a temporary solution until nixpkgs us up-to-date again
    uv2nix.inputs.nixpkgs.url = "github:runtimeverification/nixpkgs/libmatch";
    # inputs.nixpkgs.follows = "nixpkgs";
    pyproject-build-systems.url = "github:pyproject-nix/build-system-pkgs/7dba6dbc73120e15b558754c26024f6c93015dd7";
    pyproject-build-systems = {
      inputs.nixpkgs.follows = "uv2nix/nixpkgs";
      inputs.uv2nix.follows = "uv2nix";
      inputs.pyproject-nix.follows = "uv2nix/pyproject-nix";
    };
    pyproject-nix.follows = "uv2nix/pyproject-nix";
  };
  outputs = {
      self,
      k-framework,
      haskell-backend,
      nixpkgs,
      flake-utils,
      blockchain-k-plugin,
      rv-nix-tools,
      uv2nix,
      pyproject-build-systems,
      pyproject-nix,
      ... }:
  let
    pythonVer = "310";
    nixLibs = pkgs: with pkgs; "-I${openssl.dev}/include -L${openssl.out}/lib -I${secp256k1}/include -L${secp256k1}/lib";
  in flake-utils.lib.eachDefaultSystem (system:
    let
      uvOverlay = final: prev: {
        uv = uv2nix.packages.${final.system}.uv-bin;
      };
      # create custom overlay for k, because the overlay in k-framework currently also includes a lot of other stuff instead of only k
      kOverlay = final: prev: {
        k = k-framework.packages.${final.system}.k;
      };
      haskellBackendOverlay = final: prev: {
        kore-exec = haskell-backend.packages.${final.system}.kore-exec;
      };
      kevmOverlay = final: prev:
      let
        python = final."python${pythonVer}";
        kevm-pyk = final.callPackage ./nix/kevm-pyk {
          inherit pyproject-nix pyproject-build-systems uv2nix python;
        };
        kevm = final.callPackage ./nix/kevm {
          inherit kevm-pyk python;
          rev = self.rev or null;
        };
        kevm-test = final.callPackage ./nix/kevm/test.nix { };
        kevm-profile = final.callPackage ./package/nix/profile.nix { };
      in {
        inherit kevm kevm-test kevm-profile;
      };
      pkgs = import nixpkgs {
        inherit system;
        overlays = [
          uvOverlay
          kOverlay
          haskellBackendOverlay
          kevmOverlay
          blockchain-k-plugin.overlay
        ];
      };
      python = pkgs."python${pythonVer}";
    in {
      devShells.default = pkgs.mkShell {
        packages = with pkgs; ([
          k
          autoconf
          automake
          cmake
          pkg-config
          python
          makeWrapper
          clang
          python
          uv
          which
        ] ++ lib.optionals (!stdenv.isDarwin) [
          elfutils
        ]);
        buildInputs = with pkgs; [
          fmt
          libtool
          mpfr
          openssl
          secp256k1
          boost
        ];
        env = {
          # prevent uv from managing Python downloads and force use of specific 
          UV_PYTHON_DOWNLOADS = "never";
          UV_PYTHON = python.interpreter;
        };
        shellHook = ''
          export NIX_LIBS="${nixLibs pkgs}"
          unset PYTHONPATH
        '' + pkgs.lib.strings.optionalString (pkgs.stdenv.isAarch64 && pkgs.stdenv.isDarwin) ''
          export APPLE_SILICON=true
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

      packages = rec {
        inherit (pkgs) kevm-pyk kevm kevm-test;
        default = kevm;
        profile = pkgs.kevm-profile;

        check-submodules = rv-nix-tools.lib.check-submodules pkgs {
          inherit k-framework blockchain-k-plugin;
        };

        update-from-submodules =
          rv-nix-tools.lib.update-from-submodules pkgs ./flake.lock {
            blockchain-k-plugin.submodule = "deps/plugin";
          };
      };
    }) // {
      overlays.default = final: prev: {
        inherit (self.packages.${final.system}) kevm;
      };
    };
}
