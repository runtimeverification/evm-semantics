{
  description = "A flake for the KEVM Semantics";

  inputs = {
    rv-nix-tools.url = "github:runtimeverification/rv-nix-tools/854d4f05ea78547d46e807b414faad64cea10ae4";
    nixpkgs.follows = "rv-nix-tools/nixpkgs";

    k-framework.url = "github:runtimeverification/k/v7.1.297";
    k-framework.inputs.nixpkgs.follows = "nixpkgs";
    flake-utils.follows = "k-framework/flake-utils";
    blockchain-k-plugin = {
      url =
        "github:runtimeverification/blockchain-k-plugin/f159396d0f16b88c86c557c47f7ae36ffc59dc53";
      inputs.flake-utils.follows = "k-framework/flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    haskell-backend.follows = "k-framework/haskell-backend";
    uv2nix.url = "github:pyproject-nix/uv2nix/b6ed0901aec29583532abe65117b18d86a49b617";
    # uv2nix requires a newer version of nixpkgs
    # therefore, we pin uv2nix specifically to a newer version of nixpkgs
    # until we replaced our stale version of nixpkgs with an upstream one as well
    # but also uv2nix requires us to call it with `callPackage`, so we add stuff
    # from the newer nixpkgs to our stale nixpkgs via an overlay
    nixpkgs-unstable.url = "github:NixOS/nixpkgs/nixos-unstable";
    uv2nix.inputs.nixpkgs.follows = "nixpkgs-unstable";
    # uv2nix.inputs.nixpkgs.follows = "nixpkgs";
    pyproject-build-systems.url = "github:pyproject-nix/build-system-pkgs/dbfc0483b5952c6b86e36f8b3afeb9dde30ea4b5";
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
      nixpkgs-unstable,
      ... }:
  let
    pythonVer = "310";
    nixLibs = pkgs: with pkgs; "-I${openssl.dev}/include -L${openssl.out}/lib -I${secp256k1}/include -L${secp256k1}/lib";
  in flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs-unstable = import nixpkgs-unstable {
        inherit system;
      };
      # for uv2nix, remove this once we updated to a newer version of nixpkgs
      staleNixpkgsOverlay = final: prev: {
        inherit (pkgs-unstable) replaceVars;
      };
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
        kevm-pyk-pyproject = final.callPackage ./nix/kevm-pyk-pyproject {
          inherit uv2nix;
        };
        kevm-pyk = final.callPackage ./nix/kevm-pyk {
          inherit pyproject-nix pyproject-build-systems kevm-pyk-pyproject python;
          pyproject-overlays = [
            (k-framework.overlays.pyk-pyproject system)
          ];
        };
        kevm = final.callPackage ./nix/kevm {
          inherit kevm-pyk python;
          rev = self.rev or null;
        };
        kevm-test = final.callPackage ./nix/kevm/test.nix { };
        kevm-profile = final.callPackage ./package/nix/profile.nix { };
      in {
        inherit kevm kevm-test kevm-profile kevm-pyk-pyproject;
      };
      pkgs = import nixpkgs {
        inherit system;
        overlays = [
          staleNixpkgsOverlay
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
        inherit (pkgs) kevm-pyk kevm kevm-test kevm-pyk-pyproject;
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
      overlays = {
        default = final: prev: {
          inherit (self.packages.${final.system}) kevm;
        };
        # this pyproject-nix overlay allows for overriding the python packages that are otherwise locked in `uv.lock`
        # by using this overlay in dependant nix flakes, you ensure that nix overrides also override the python package     
        pyk-pyproject = system: final: prev: {
          inherit (self.packages.${system}.kevm-pyk-pyproject.lockFileOverlay final prev) kevm-pyk;
        };
      };
    };
}
