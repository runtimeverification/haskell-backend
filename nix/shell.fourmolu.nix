let
  default = import ../default.nix {};
  fourmolu = import ./fourmolu.nix {};
  inherit (default) pkgs;
  inherit (pkgs) fd;
in

pkgs.mkShell {
  buildInputs = [ fourmolu fd ];
}
