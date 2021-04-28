let
  default = import ../default.nix {};
  inherit (default) pkgs;
  inherit (pkgs) jq miller;
in

pkgs.mkShell {
  buildInputs = [ jq miller ];
}
