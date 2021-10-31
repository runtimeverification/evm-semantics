let
  sources = import ./nix/sources.nix {};
  pinned = import sources."nixpkgs" {};
in

{ pkgs ? pinned
, release ? null
}:

let release_ = release; in

let
  inherit (pkgs) lib;
  ttuegel = import sources."nix-lib" { inherit pkgs; };

  release = if release_ == null then pkgs.stdenv.isLinux else false;

  kframework =
    let
      tag = lib.fileContents ./deps/k_release;
      url = "https://github.com/kframework/k/releases/download/${tag}/release.nix";
      args = import (builtins.fetchurl { inherit url; });
      src = pkgs.fetchgit args;
    in import src { inherit release; };
  #kframework = import ./../k { inherit pkgs release; };
  inherit (kframework) k haskell-backend clang;
  # The following llvm-backend directory is needed at build time by kevm, but it's missing
  # from the llvm-backend nix package, so we override the postInstall phase to copy it in
  # the nix store.
  # NOTE: Move this to the llvm-backend repository?
  llvm-backend = kframework.llvm-backend.overrideAttrs (old:
    { postInstall = if old ? postInstall then old.postInstall else "" + ''
        mkdir -p $out/lib/cmake/kframework
        cp -r ../cmake/* $out/lib/cmake/kframework/;
        '';
    }
  );
  llvmPackages = pkgs.llvmPackages_10;
in

let
  inherit (pkgs) callPackage;
in

let
  src = ttuegel.cleanGitSubtree {
    name = "evm-semantics";
    src = ./.;
  };
  libff = callPackage ./nix/libff.nix {
    stdenv = llvmPackages.stdenv;
    src = ttuegel.cleanGitSubtree {
      name = "libff";
      src = ./.;
      subDir = "deps/plugin/deps/libff";
    };
  };
  kevm = callPackage ./nix/kevm.nix {
    inherit src;
    inherit (ttuegel) cleanSourceWith;
    inherit libff;
    inherit k haskell-backend llvm-backend clang;
    inherit (pkgs.python2Packages) python;
  };
  default =
    {
      inherit kevm;
    };
in default
