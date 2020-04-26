{ default ? import ./default.nix {} }:

let
  inherit (default) project pkgs;
in

project.shellFor {
  additional = hspkgs:
    [
      hspkgs.ghc-tags-plugin
      hspkgs.terminfo
    ];
  buildInputs =
    with pkgs;
    [
      ghcid ghcide gnumake hlint stylish-haskell yq z3
    ];
  exactDeps = true;
}
