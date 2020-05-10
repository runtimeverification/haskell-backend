{ default ? import ./default.nix {} }:

let
  inherit (default) project pkgs;
  local =
    if builtins.pathExists ./shell.local.nix
    then import ./shell.local.nix { inherit default; }
    else x: x;
  shellFor = args: project.shellFor (local args);
  stylish-haskell = (pkgs.haskell-nix.hackage-package { name = "stylish-haskell"; version = "0.11.0.0"; }).components.exes.stylish-haskell;
in

shellFor {
  buildInputs =
    with pkgs;
    [
      ghcid ghcide gnumake hlint stylish-haskell yq z3
    ];
}
