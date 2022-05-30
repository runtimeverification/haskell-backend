{
  description = "K Kore Language Haskell Backend";
  inputs = {
    haskell-nix.url = "github:input-output-hk/haskell.nix";
    nixpkgs.follows = "haskell-nix/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    z3src = {
      url = "github:Z3Prover/z3/z3-4.8.15";
      flake = false;
    };
  };
  outputs = { self, nixpkgs, flake-utils, haskell-nix, z3src }:
    flake-utils.lib.eachSystem [
      "x86_64-linux"
      "aarch64-linux"
      "x86_64-darwin"
      "aarch64-darwin"
    ] (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          inherit (haskell-nix) config;
        };
        haskell-backend =
          haskell-nix.legacyPackages.${system}.haskell-nix.stackProject {
            src = ./.;
            materialized = ./nix/kore.nix.d;
            compiler-nix-name = "ghc8107";
          };
        version = haskell-backend.kore.components.exes.kore-exec.version;
      in {
        defaultPackage = pkgs.symlinkJoin {
          name = "kore-${version}";
          paths = pkgs.lib.attrValues haskell-backend.kore.components.exes;
        };
        devShell = haskell-backend.shellFor {
          buildInputs = with pkgs; [
            gnumake
            fd
            z3
            # hls-renamed
            ghcid
            hlint
            # fourmolu
            cabal-install
            stack
          ];
        };
      }) // {
        prelude-kore = ./src/main/kore/prelude.kore;
        overlay = nixpkgs.lib.composeManyExtensions [
          haskell-nix.overlay

          (final: prev: {
            # This overlay adds our project to pkgs
            k-haskell-backend = prev.haskell-nix.stackProject {
              src = prev.haskell-nix.haskellLib.cleanGit {
                name = "k-haskell-backend-src";
                src = ./.;
              };
              compiler-nix-name = "ghc8107";
            };
          })

          (final: prev: {
            z3 = prev.z3.overrideAttrs (old: {
              src = z3src;
              version =
                # hacky way of keeping the version number of this derivation consistent with
                # the z3src input.
                let lock = builtins.fromJSON (builtins.readFile ./flake.lock);
                in builtins.replaceStrings [ "z3-" ] [ "" ]
                lock.nodes.z3src.original.ref;
            });
          })
        ];
      };
}
