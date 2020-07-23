{ default ? import ./default.nix {} }:

let
  inherit (default) project;

  local =
    if builtins.pathExists ./shell.local.nix
    then import ./shell.local.nix { inherit default; }
    else x: x;
  shellFor = args: project.shellFor (local args);

  inherit (default.pkgs) ghcide hie-bios;

  sources = import ./nix/sources.nix;
  pkgs = import sources."nixpkgs" {};
  inherit (pkgs) stack;
in

shellFor {
  buildInputs =
    with pkgs;
    [
      gnumake yq z3
      ghcid
      ghcide hie-bios
      haskellPackages.ghc-events
      stack
    ];
  tools = {
    cabal = "3.2.0.0";
    hlint = "3.1";
    stylish-haskell = "0.11.0.0";
  };
}
