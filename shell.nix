{ default ? import ./default.nix {}
, checkMaterialization ? false
}:

let
  inherit (default) project;
  inherit (project) shellFor;

  sources = import ./nix/sources.nix;
  pkgs = import sources."nixpkgs" {};

  inherit (pkgs) cabal-install ghcid stack;
  inherit (pkgs) fd gnumake yq z3;

  inherit (default) compiler-nix-name index-state;

  hls-project = import sources."nix-haskell-hls" {
    ghcVersion = compiler-nix-name;
  };
  inherit (hls-project) hls-renamed;

  hlint-project = default.pkgs.haskell-nix.cabalProject {
    src = sources."hlint";
    inherit checkMaterialization compiler-nix-name index-state;
    materialized = ./nix/hlint.nix.d;
  };
  inherit (hlint-project.hlint.components.exes) hlint;

  fourmolu = import ./nix/fourmolu.nix { inherit default checkMaterialization; };

in

shellFor {
  buildInputs =
    [
      gnumake fd z3
      hls-renamed
      ghcid hlint fourmolu
      cabal-install stack
    ];
  passthru.rematerialize = pkgs.writeScript "rematerialize-shell.sh" ''
    #!/bin/sh
    ${hlint-project.plan-nix.passthru.updateMaterialized}
    ${fourmolu.passthru.updateMaterialized}
  '';
}
