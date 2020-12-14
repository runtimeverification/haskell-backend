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

  project = pkgs.haskell-nix.stackProject {
    src =
      # Despite the haskell.nix documentation, do not use cleanGit!
      # The kore repository is imported as a Git submodule, but cleanGit does 
      # not support submodules.
      let 
        patterns = [
          "/*"
          "!/stack.yaml"
          "!/kore"
        ];
      in
        pkgs.nix-gitignore.gitignoreSourcePure patterns ./.;
    inherit checkMaterialization;
    materialized = ./nix/kore.nix.d;
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

  shell = import ./shell.nix { inherit default checkMaterialization; };

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
