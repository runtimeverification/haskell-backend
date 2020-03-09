{ default ? import ./default.nix }:

let
  inherit (default) project pkgs;
in

project.shellFor {
  buildInputs = with pkgs; [ ghcide-ghc865 ];
}
