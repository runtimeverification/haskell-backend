{ default ? import ./default.nix {} }:

let
  inherit (default) project pkgs;
  local =
    if builtins.pathExists ./shell.local.nix
    then import ./shell.local.nix { inherit default; }
    else x: x;
  shellFor = args: project.shellFor (local args);
in

shellFor {
  buildInputs =
    with pkgs;
    [
      ghcid ghcide gnumake hlint stylish-haskell yq z3
    ];
  exactDeps = true;
}
