{ default ? import ./default.nix {}
, checkMaterialization ? false
}:

let
  inherit (default) project;
  inherit (project) shellFor;

  sources = import ./nix/sources.nix;
  pkgs = import sources."nixpkgs" {};

  inherit (pkgs) cabal-install ghcid stack;
  inherit (pkgs) gnumake yq z3;

  # Change the compiler when updating our own resolver.
  compiler-nix-name = "ghc8103";
  index-state = "2021-02-09T00:00:00Z";

  ghcide-project = default.pkgs.haskell-nix.cabalProject {
    src = sources."ghcide";
    modules = [
      # This fixes a performance issue, probably https://gitlab.haskell.org/ghc/ghc/issues/15524
      { packages.ghcide.configureFlags = [ "--enable-executable-dynamic" ]; }
    ];
    inherit checkMaterialization compiler-nix-name index-state;
    materialized = ./nix/ghcide.nix.d;
  };
  inherit (ghcide-project.ghcide.components.exes) ghcide;
  inherit (ghcide-project.hie-bios.components.exes) hie-bios;

  hlint-project = default.pkgs.haskell-nix.cabalProject {
    src = sources."hlint";
    inherit checkMaterialization compiler-nix-name index-state;
    materialized = ./nix/hlint.nix.d;
  };
  inherit (hlint-project.hlint.components.exes) hlint;

  stylish-haskell-project = default.pkgs.haskell-nix.cabalProject {
    src = sources."stylish-haskell";
    inherit checkMaterialization compiler-nix-name index-state;
    materialized = ./nix/stylish-haskell.nix.d;
  };
  inherit (stylish-haskell-project.stylish-haskell.components.exes) stylish-haskell;

  hpack-project = default.pkgs.haskell-nix.cabalProject {
    src = sources."hpack";
    inherit checkMaterialization compiler-nix-name index-state;
    materialized = ./nix/hpack.nix.d;
  };
  inherit (hpack-project.hpack.components.exes) hpack;

in

shellFor {
  buildInputs =
    [
      gnumake yq z3
      ghcide hie-bios
      ghcid hlint hpack stylish-haskell
      cabal-install stack
    ];
  passthru.rematerialize = pkgs.writeScript "rematerialize-shell.sh" ''
    #!/bin/sh
    ${ghcide-project.plan-nix.passthru.updateMaterialized}
    ${hlint-project.plan-nix.passthru.updateMaterialized}
    ${stylish-haskell-project.plan-nix.passthru.updateMaterialized}
    ${hpack-project.plan-nix.passthru.updateMaterialized}
  '';
}
