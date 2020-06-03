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
      ghcid gnumake yq z3
      ghcide hie-bios
    ];
  tools = {
    cabal = "3.2.0.0";
    hlint = "3.1";
    stylish-haskell = "0.11.0.0";
  };
}
