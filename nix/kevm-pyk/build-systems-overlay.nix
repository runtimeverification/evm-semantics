final: prev:
let
  inherit (final) resolveBuildSystem;
  inherit (builtins) mapAttrs;

  # Build system dependencies specified in the shape expected by resolveBuildSystem
  # The empty lists below are lists of optional dependencies.
  #
  # A package `foo` with specification written as:
  # `setuptools-scm[toml]` in pyproject.toml would be written as
  # `foo.setuptools-scm = [ "toml" ]` in Nix
  buildSystemOverrides = {
    # add dependencies here, e.g.:
    # pyperclip.setuptools = [ ];
  };
in
mapAttrs (
  name: spec:
  prev.${name}.overrideAttrs (old: {
    nativeBuildInputs = old.nativeBuildInputs ++ resolveBuildSystem spec;
  })
) buildSystemOverrides
