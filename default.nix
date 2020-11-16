{ profiling ? false
, release ? false
, threaded ? !profiling
, checkMaterialization ? false
}:

let
  sources = import ./nix/sources.nix;

  pkgs =
    let
      haskell-nix = import sources."haskell.nix" {};
      inherit (haskell-nix) nixpkgsArgs;
      args = nixpkgsArgs // { };
    in import haskell-nix.sources.nixpkgs-2003 args;
  inherit (pkgs) lib;

  local =
    if builtins.pathExists ./local.nix
    then import ./local.nix { inherit default; }
    else x: x;

  project =
    (args: pkgs.haskell-nix.stackProject (local args)) {
      src = pkgs.haskell-nix.haskellLib.cleanGit { name = "kore"; src = ./.; };
      inherit checkMaterialization;
      materialized = ./nix/kore.materialized;
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

            # Add Z3 to PATH for unit tests.
            components.tests.kore-test.preCheck = ''
              export PATH="$PATH''${PATH:+:}${lib.getBin pkgs.z3}/bin"
            '';
          };
        }
      ];
    };

  shell = import ./shell.nix { inherit default; };

  version = project.kore.components.exes.kore-exec.version;

  default =
    {
      inherit pkgs project;
      cache = [
        project.roots
        (pkgs.haskell-nix.withInputs shell)
      ];
      kore = pkgs.symlinkJoin {
        name = "kore-${version}";
        paths = pkgs.lib.attrValues project.kore.components.exes;
      };
    };

in default
