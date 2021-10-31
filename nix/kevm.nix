{ stdenv, lib, src, cleanSourceWith
, protobuf
, cryptopp, libff, mpfr, secp256k1
, jemalloc, libffi, ncurses
, k, haskell-backend, llvm-backend, clang, python, cmake, which
}:

let src' = src; in

let
  version = "0";

  src = cleanSourceWith {
    name = "evm-semantics";
    src = src';
    ignore = [
      "*.nix"
      "/.build"
      "/deps/k"
      "/deps/plugin/deps"
      "/media"
      "/nix"
      "/package"
      "/web"
    ];
  };
  mkEVM = target: f: stdenv.mkDerivation (f {
    pname = "evm-${target}";
    inherit version;
    src = cleanSourceWith {
      name = "evm-semantics";
      inherit src;
    };
    nativeBuildInputs = [ protobuf k haskell-backend llvm-backend clang cmake which ];
    buildInputs = [ cryptopp libff mpfr secp256k1 ];

    postPatch = ''
        patchShebangs ./kevm
      '';
    dontConfigure = true;
    makeFlags =
      [
        "INSTALL_PREFIX=${builtins.placeholder "out"}"
        "SKIP_LLVM=true"
        "SKIP_HASKELL=true"
        "SYSTEM_LIBFF=true"
        "SYSTEM_LIBSECP256K1=true"
        "SYSTEM_LIBCRYPTOPP=true"
      ];
    buildFlags = [ "build-${target}" ];
    installPhase = ''
        mkdir -p $out/bin
        cp .build/${builtins.placeholder "out"}/lib/kevm/node/build/kevm-${target} $out/bin/
      '';
  });

  kevm-vm = mkEVM "vm" (x: x);

  host-PATH = lib.makeBinPath [ k llvm-backend haskell-backend ];

in
  stdenv.mkDerivation {
    pname = "kevm";
    inherit version src;
    nativeBuildInputs = [ protobuf k haskell-backend llvm-backend clang cmake which ];
    buildInputs = [ cryptopp libff mpfr secp256k1  ];

    dontConfigure = true;
    postPatch = ''
        sed -i kevm \
          -e "/^INSTALL_BIN=/ c INSTALL_BIN=\"$out/bin\"" \
          -e "/^export LD_LIBRARY_PATH=/ d" \
          -e '2 i export PATH="${host-PATH}:$PATH"'

        patchShebangs ./kevm
      '';
    makeFlags = [
      "INSTALL_PREFIX=${builtins.placeholder "out"}"
      "SKIP_LLVM=true"
      "SKIP_HASKELL=true"
      "SYSTEM_LIBFF=true"
      "SYSTEM_LIBSECP256K1=true"
      "SYSTEM_LIBCRYPTOPP=true"
    ];
    buildFlags = [ "build-kevm" ];
    installPhase = ''
      cp -r .build/${builtins.placeholder "out"} $out
      ln -s ${kevm-vm}/bin/kevm-vm $out/bin/
    '';
    passthru = {
      inherit kevm-vm;
    };
  }
