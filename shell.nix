{ default ? import ./default.nix }:

let
  inherit (default) project pkgs;
in

project.shellFor {
  buildInputs =
    with pkgs;
    [
      ghcid ghcide gnumake hlint stylish-haskell yq z3
    ];
}
