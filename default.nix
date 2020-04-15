{ profiling ? false
, release ? false
, threaded ? !profiling
}:

let
  sources = import ./nix/sources.nix;
  haskell-nix = import sources."haskell.nix" {};
  nixpkgs =
    let
      inherit (haskell-nix) nixpkgsArgs;
      args = nixpkgsArgs // {
        overlays =
          (nixpkgsArgs.overlays or [])
          ++ [ (import ./nix/ghcide.nix { inherit sources; }) ]
          ++ [ (import ./nix/stylish-haskell.nix { inherit sources; }) ]
          ;
        config =
          (nixpkgsArgs.config or {})
          ;
      };
    in import haskell-nix.sources.nixpkgs-1909 args;
  pkgs = nixpkgs;
  project =
    pkgs.haskell-nix.stackProject {
      src = pkgs.haskell-nix.haskellLib.cleanGit { name = "kore"; src = ./.; };
      modules = [
        {
          # package *
          enableLibraryProfiling = true;
          profilingDetail = "none";
          # package kore
          packages.kore = {
            flags = {
              inherit release threaded;
            };
            enableLibraryProfiling = profiling;
            enableExecutableProfiling = profiling;
            profilingDetail = "toplevel-functions";
          };
        }
      ];
    };
  shell = import ./shell.nix { inherit default; };
  default =
    {
      inherit pkgs project;
      cache = [
        pkgs.haskell-nix.haskellNixRoots
        (pkgs.haskell-nix.withInputs shell)
      ];
    };

in default
