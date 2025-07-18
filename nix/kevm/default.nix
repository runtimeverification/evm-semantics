{
  lib,
  stdenv,
  runCommand,
  makeWrapper,
  callPackage,

  k,
  autoconf,
  automake,
  cmake,
  clang,
  fmt,
  libtool,
  mpfr,
  openssl,
  pkg-config,
  secp256k1,
  elfutils,
  which,
  boost,

  python,
  kevm-pyk,
  rev ? null
} @ args:
let
  nixLibs = "-I${openssl.dev}/include -L${openssl.out}/lib -I${secp256k1}/include -L${secp256k1}/lib";
in
stdenv.mkDerivation {
  pname = "kevm";
  version = if (rev != null) then rev else "dirty";
  nativeBuildInputs = [
    k
    autoconf
    automake
    cmake
    pkg-config
    kevm-pyk
    python
    makeWrapper
     # this does *not* causes this derivation to be built with clang
     # but it's required because the program `ar` provided by gcc crashes the plugin Makefile
     # due to some directory disappearing during the build that the make process is inside
    clang
  ] ++ lib.optionals (!stdenv.isDarwin) [
    elfutils
  ];
  buildInputs = [
    fmt
    libtool
    mpfr
    openssl
    secp256k1
    boost
  ];

  src = callPackage ../kevm-source { };

  dontUseCmakeConfigure = true;

  enableParallelBuilding = true;

  buildPhase = ''
    XDG_CACHE_HOME=$(pwd) NIX_LIBS="${nixLibs}" ${
      lib.optionalString
      (stdenv.isAarch64 && stdenv.isDarwin)
      "APPLE_SILICON=true"
    } kevm-kdist -v build -j4
  '';

  installPhase = ''
    mkdir -p $out
    cp -r ./kdist-*/* $out/
    mkdir -p $out/bin
    makeWrapper ${kevm-pyk}/bin/kevm $out/bin/kevm --prefix PATH : ${
      lib.makeBinPath [
        which
        k
      ]
    } --set NIX_LIBS "${nixLibs}" --set KDIST_DIR $out
  '';
}