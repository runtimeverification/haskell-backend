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

  ghcide-project = default.pkgs.haskell-nix.project {
    src = sources."ghcide";
    projectFileName = "stack810.yaml";
    modules = [
      # This fixes a performance issue, probably https://gitlab.haskell.org/ghc/ghc/issues/15524
      { packages.ghcide.configureFlags = [ "--enable-executable-dynamic" ]; }
    ];
    inherit checkMaterialization;
    materialized = ./nix/ghcide.nix.d;
  };
  inherit (ghcide-project.ghcide.components.exes) ghcide;
  inherit (ghcide-project.hie-bios.components.exes) hie-bios;

  hlint-project = default.pkgs.haskell-nix.stackProject {
    src = sources."hlint";
    inherit checkMaterialization;
    materialized = ./nix/hlint.nix.d;
  };
  inherit (hlint-project.hlint.components.exes) hlint;

  stylish-haskell-project = default.pkgs.haskell-nix.stackProject {
    src = sources."stylish-haskell";
    inherit checkMaterialization;
    materialized = ./nix/stylish-haskell.nix.d;
  };
  inherit (stylish-haskell-project.stylish-haskell.components.exes) stylish-haskell;

  hpack-project = default.pkgs.haskell-nix.cabalProject {
    src = sources."hpack";
    # Change the compiler when updating our own resolver.
    compiler-nix-name = "ghc8103";
    inherit checkMaterialization;
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
    ${ghcide-project.stack-nix.passthru.updateMaterialized}
    ${hlint-project.stack-nix.passthru.updateMaterialized}
    ${stylish-haskell-project.stack-nix.passthru.updateMaterialized}
    ${hpack-project.plan-nix.passthru.updateMaterialized}
  '';
}
