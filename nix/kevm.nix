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

  mkEVM = target: f: stdenv.mkDerivation (f {
    pname = "kevm-${target}";
    inherit version;
    src = cleanSourceWith {
      name = "evm-semantics";
      inherit src;
    };
    nativeBuildInputs = [ protobuf k haskell-backend llvm-backend clang cmake ];
    buildInputs = [ cryptopp libff mpfr secp256k1 ];
    makeFlags =
      [
        "SKIP_LLVM=true"
        "SKIP_HASKELL=true"
        "SYSTEM_LIBFF=true"
        "SYSTEM_LIBSECP256K1=true"
        "SYSTEM_LIBCRYPTOPP=true"
      ];
    dontConfigure = true;
    dontPatch = true;
    preBuild = ''
        patchShebangs ./kevm
      '';
    buildFlags = [ "build-${target}" ];
    # installTargets = [ "install-${target}" ];
  });

  evm-vm = mkEVM "vm" (x: x);

  host-PATH = lib.makeBinPath [ k llvm-backend haskell-backend ];

in
stdenv.mkDerivation {
  pname = "kevm";
  inherit version src;
  nativeBuildInputs = [ k python ];
  makeFlags = [
  ];
  buildFlags = [ "build-kevm" ];
#   installTargets = [ "install-kiele" ];
   postInstall = ''
     ln -s ${lib.getLib evm-vm}/lib/kevm/node $out/lib/kevm
   '';
  passthru = { inherit evm-vm; };
}
