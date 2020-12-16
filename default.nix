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
        inherit (pkgs.nix-gitignore) gitignoreFilterPure;
      in
        # Give a fixed name ("kore") to the current directory.
        # When imported as a submodule with a different name, the store path
        # of the source code would be different. For example, in
        # kframework/kore it might be
        #     /nix/store/00000000000000000000000000000000-kore
        # but when imported as a submodule of kframework/k, it might be
        #     /nix/store/00000000000000000000000000000000-haskell-backend
        # This would change the hash of the build products and ruin caching.
        builtins.path {
          path = ./.;
          name = "kore";
          filter = gitignoreFilterPure (_: _: true) patterns ./.;
        };
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
