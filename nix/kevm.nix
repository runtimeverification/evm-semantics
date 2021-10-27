{ stdenv, lib, src, cleanSourceWith
, protobuf
, cryptopp, libff, mpfr, secp256k1
, jemalloc, libffi, ncurses
, k, haskell-backend, llvm-backend, clang, python, cmake, bash
}:

let src' = src; in

let
  version = "0.2.0";

  src = cleanSourceWith {
    name = "evm-semantics";
    src = src';
    ignore = [
      "*.nix"
      "/nix"
      "/package"
      "/tests"
      "/web"
    ];
  };

  host-PATH = lib.makeBinPath [ k llvm-backend haskell-backend ];
in
stdenv.mkDerivation {
  pname = "kevm";
  inherit version src;
  nativeBuildInputs = [ protobuf k haskell-backend llvm-backend clang cmake python ];
  buildInputs = [ cryptopp libff mpfr secp256k1 ];
  makeFlags = [
    "INSTALL_PREFIX=${builtins.placeholder "out"}"
    "SKIP_LLVM=true"
    "SKIP_HASKELL=true"
    "SYSTEM_LIBFF=true"
    "SYSTEM_LIBSECP256K1=true"
    "SYSTEM_LIBCRYPTOPP=true"
  ];
  dontConfigure = true;
  postPatch = ''
      patchShebangs ./kevm
    '';
  buildFlags = [ "build" ];
}
