{ default ? import ./default.nix {} }:

let
  inherit (default) project;
  inherit (project) shellFor;

  sources = import ./nix/sources.nix;
  pkgs = import sources."nixpkgs" {};

  inherit (pkgs) cabal-install ghcid stack;
  inherit (pkgs) gnumake yq z3;

  ghcide-project = default.pkgs.haskell-nix.project {
    src = sources."ghcide";
    projectFileName = "stack810.yaml";
    modules = [
      # This fixes a performance issue, probably https://gitlab.haskell.org/ghc/ghc/issues/15524
      { packages.ghcide.configureFlags = [ "--enable-executable-dynamic" ]; }
    ];
  };
  inherit (ghcide-project.ghcide.components.exes) ghcide;
  inherit (ghcide-project.hie-bios.components.exes) hie-bios;

  hlint-project = default.pkgs.haskell-nix.stackProject {
    src = sources."hlint";
  };
  inherit (hlint-project.hlint.components.exes) hlint;

  stylish-haskell-project = default.pkgs.haskell-nix.stackProject {
    src = sources."stylish-haskell";
  };
  inherit (stylish-haskell-project.stylish-haskell.components.exes) stylish-haskell;

in

shellFor {
  buildInputs =
    [
      gnumake yq z3
      ghcide hie-bios
      ghcid hlint stylish-haskell
      cabal-install stack
    ];
}
