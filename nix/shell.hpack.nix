let
  default = import ../default.nix {};
  hpack = import ./hpack.nix {};
in

default.pkgs.mkShell {
  buildInputs = [ hpack ];
}
