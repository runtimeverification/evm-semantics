{
  stdenv,
  callPackage,

  which,
  git,

  kevm,
  rev ? null
}:

stdenv.mkDerivation {
  pname = "kevm-test";
  version = if (rev != null) then rev else "dirty";

  src = callPackage ../kevm-source { };

  enableParallelBuilding = true;

  buildInputs = [
    kevm
    which
    git
  ];

  buildPhase = ''
    chmod -R u+w tests
    APPLE_SILICON=${
        if stdenv.isAarch64 && stdenv.isDarwin then
          "true"
        else
          "false"
    } NIX=true package/test-package.sh
  '';

  installPhase = ''
    touch $out
  '';
}