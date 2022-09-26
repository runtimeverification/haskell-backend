{ default ? import ../default.nix { }, checkMaterialization ? false }:

let
  sources = import ./sources.nix;

  inherit (default) compiler-nix-name index-state;

  fourmolu-project = default.pkgs.haskell-nix.cabalProject {
    src = sources."fourmolu";
    inherit checkMaterialization compiler-nix-name index-state;
    materialized = ./fourmolu.nix.d;
  };

  inherit (fourmolu-project.fourmolu.components.exes) fourmolu;

in fourmolu // {
  passthru = (fourmolu.passthru or { }) // {
    inherit (fourmolu-project.plan-nix.passthru) updateMaterialized;
  };
}
