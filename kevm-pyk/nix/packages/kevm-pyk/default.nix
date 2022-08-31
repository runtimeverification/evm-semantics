# WARNING: This file was automatically generated. You should avoid editing it.
# If you run pynixify again, the file will be either overwritten or
# deleted, and you will lose the changes you made to it.

{ buildPythonPackage, fetchPypi, lib, pyk }:

buildPythonPackage rec {
  pname = "kevm-pyk";
  version = "0.1.dev0";

  src = lib.cleanSource ../../..;

  propagatedBuildInputs = [ pyk ];

  # TODO FIXME
  doCheck = false;

  meta = with lib; { };
}
