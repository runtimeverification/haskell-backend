{
  description = "K Kore Language backend";
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
    let
      overlays = [
        haskell-nix.overlay

        (final: prev: {
          # This overlay adds our project to pkgs
          k-haskell-backend =
            prev.haskell-nix.stackProject {
              src = prev.haskell-nix.haskellLib.cleanGit {
                name = "k-haskell-backend-src";
                src = ./.;
              };
              materialized = ./nix/kore.nix.d;
              compiler-nix-name = "ghc8107";
            };
        })

        (final: prev: {
          z3 = prev.z3.overrideAttrs (old: {
            src = z3src;
            version =
              # hacky way of keeping the version number of this derivation consistent with
              # the z3src input.
              let
                lock = builtins.fromJSON (builtins.readFile ./flake.lock);
              in
                builtins.replaceStrings ["z3-"] [""] lock.nodes.z3src.original.ref;
          });
        })
      ];
      finalFlake = flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
        let
          pkgs = import nixpkgs { inherit system overlays; inherit (haskell-nix) config; };
          flake = pkgs.k-haskell-backend.flake { };

          # add z3 to the path for the runtime
          # very flake-y (pun intended) atm, need to invesitgate why it crashes with segfaults
          # when ran via `nix run .#kore:test:kore-test`
          # kore-test-with-z3 = pkgs.symlinkJoin {
          #   name = "kore-test";
          #   paths = [ flake.packages."kore:test:kore-test" ];
          #   buildInputs = [ pkgs.makeWrapper ];
          #   postBuild = ''
          #     wrapProgram $out/bin/kore-test \
          #     --set PATH ${pkgs.lib.makeBinPath [ pkgs.z3 ]}
          #   '';
          # };

      in
        flake // {
          prelude-kore = ./src/main/kore/prelude.kore;
          # apps = flake.apps // {
          #   "kore:test:kore-test" = {
          #     type = "app";
          #     program = "${kore-test-with-z3}/bin/kore-test";
          #   };
          # };

          devShell = pkgs.k-haskell-backend.shellFor {
            buildInputs =
              with pkgs; [
                gnumake fd z3
                # hls-renamed
                ghcid hlint
                # fourmolu
                cabal-install stack
              ];
          };
        }
    );

    pkgs = import nixpkgs { };
  in
    finalFlake // {
      overlay = nixpkgs.lib.composeManyExtensions overlays;
    };
}