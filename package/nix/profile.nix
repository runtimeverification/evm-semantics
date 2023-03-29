{ stdenv, writeScriptBin, src, kevm, time, which, kore-exec }:

let
  profile = writeScriptBin "profile" ''
    #! ${stdenv.shell}
    set -euo pipefail
    test_log="$1" ; shift
    exit_status='0'
    `${which}/bin/which ${time}/bin/time` --quiet --format '%x %es %Us %Ss %MKB %C' --output "$test_log" --append \
        "$@" &>/dev/null \
        || exit_status="$?"
    exit "$exit_status"
  '';
in stdenv.mkDerivation {
  name = "kevm-profile";
  inherit src;
  preferLocalBuild = true;
  buildInputs = [ kevm ];
  postPatch = ''
    substituteInPlace ./Makefile \
      --replace 'venv: $(VENV_DIR)/pyvenv.cfg' 'venv:'
  '';

  buildPhase = ''
    mkdir -p .build/usr
    cp -r ${kevm}/* .build/usr/
    ${kore-exec}/bin/kore-exec --version &> log
    make build-prove-haskell PYK_ACTIVATE=true -j4
    make test-prove-smoke PYK_ACTIVATE=true TEST_SYMBOLIC_BACKEND=haskell KEVM='${profile}/bin/profile log timeout 600 kevm' -j6 -k
  '';
  enableParallelBuilding = true;
  installPhase = ''
    cp log $out
  '';
}
