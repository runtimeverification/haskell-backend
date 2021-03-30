{ default ? import ../default.nix {}
, checkMaterialization ? false
}:

let
  sources = import ./sources.nix;

  inherit (default) compiler-nix-name index-state;

  hpack-project = default.pkgs.haskell-nix.cabalProject {
    src = sources."hpack";
    inherit checkMaterialization compiler-nix-name index-state;
    materialized = ./hpack.nix.d;
  };

  inherit (hpack-project.hpack.components.exes) hpack;
in

hpack // {
  passthru =
    (hpack.passthru or {})
    // { inherit (hpack-project.plan-nix.passthru) updateMaterialized; };
}
