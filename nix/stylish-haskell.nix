{ sources }:

_: pkgs:

let
  project =
    pkgs.haskell-nix.stackProject {
      src = sources."stylish-haskell";
    };
in

{
  inherit (project.stylish-haskell.components.exes) stylish-haskell;
}
