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
  local =
    if builtins.pathExists ./local.nix
    then import ./local.nix { inherit default; }
    else x: x;
  stackProject = args: pkgs.haskell-nix.stackProject (local args);
  project =
    stackProject {
      src = pkgs.haskell-nix.haskellLib.cleanGit { name = "kore"; src = ./.; };
      modules = [
        {
          packages.ghc.flags.ghci = pkgs.lib.mkForce true;
          packages.ghci.flags.ghci = pkgs.lib.mkForce true;
          reinstallableLibGhc = true;
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
      pkg-def-extras = [
        (hackage: {
          packages = {
            ghc-tags-plugin = hackage.ghc-tags-plugin."0.1.6.0".revisions.default;
            ghc-tags-core = hackage.ghc-tags-core."0.1.0.0".revisions.default;
            pipes-text = hackage.pipes-text."0.0.2.5".revisions.default;
          };
        })
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
