{ profiling ? false }:

let
  sources = import ./nix/sources.nix;
  haskell-nix = import sources."haskell.nix";
  nixpkgs =
    let
      options = haskell-nix // {
        overlays =
          (haskell-nix.overlays or [])
          ++ [ (import ./nix/ghcide.nix { inherit sources; }) ]
          ++ [ (import ./nix/stylish-haskell.nix { inherit sources; }) ]
          ;
        config =
          (haskell-nix.config or {})
          ;
      };
    in import sources."nixpkgs" options;
  pkgs = nixpkgs;
  project =
    pkgs.haskell-nix.stackProject {
      src = pkgs.haskell-nix.haskellLib.cleanGit { src = ./.; };
      modules = [
        {
          # package *
          enableLibraryProfiling = true;
          profilingDetail = "none";
          # package kore
          packages.kore = {
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
