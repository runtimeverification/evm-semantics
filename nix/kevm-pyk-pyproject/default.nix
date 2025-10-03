{
  lib,
  callPackage,

  uv2nix,
}:
let
  src = callPackage ../kevm-source { };

  # load a uv workspace from a workspace root
  workspace = uv2nix.lib.workspace.loadWorkspace {
    workspaceRoot = "${src}/kevm-pyk";
  };

  # create overlay
  lockFileOverlay = workspace.mkPyprojectOverlay {
    # prefer "wheel" over "sdist" due to maintance overhead
    # there is no bundled set of overlays for "sdist" in uv2nix, in contrast to poetry2nix
    sourcePreference = "wheel";
  };
in {
  inherit lockFileOverlay workspace;
}
