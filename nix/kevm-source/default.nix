{
  lib,
  nix-gitignore,
  stdenvNoCC,

  blockchain-k-plugin-src
}:
let
  kevm-root-source = lib.cleanSource (nix-gitignore.gitignoreSourcePure [
      ../../.gitignore
      ".github/"
      "result*"
      "*.nix"
      "kevm-pyk/"
      # do not include submodule directories that might be initialized empty or non-existent
      "/deps/"
      "/tests/ethereum-tests"
      "/web/k-web-theme"
    ] ../../.
  );
  kevm-pyk-source = lib.cleanSource (nix-gitignore.gitignoreSourcePure [
      ../../kevm-pyk/.gitignore
      # do not include submodule directories that might be initialized empty or non-existent
      "/src/kevm_pyk/kproj/plugin"
    ] ../../kevm-pyk/.
  );
in stdenvNoCC.mkDerivation {
  name = "kevm-source";

  dontUnpack = true;
  dontConfigure = true;
  dontBuild = true;

  installPhase = ''
    mkdir -p $out/kevm-pyk/src/kevm_pyk/kproj/plugin
    cp -r ${kevm-root-source}/. $out/
    cp -r ${kevm-pyk-source}/. $out/kevm-pyk/
    # add files of blockchain-k-plugin to kevm-src, as nix ignores submodules in the default configuration
    cp -r ${blockchain-k-plugin-src}/* $out/kevm-pyk/src/kevm_pyk/kproj/plugin/
  '';
}
