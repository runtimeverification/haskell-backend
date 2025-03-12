{
  description = "K Kore Language Haskell Backend";

  inputs = {
    rv-utils.url = "github:runtimeverification/rv-nix-tools";
    nixpkgs.follows = "rv-utils/nixpkgs";
    z3 = {
      url = "github:Z3Prover/z3/z3-4.13.4";
      flake = false;
    };
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, rv-utils, nixpkgs, z3, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
    let
      allCabalHashesOverlay = final: prev: {
        all-cabal-hashes = final.fetchurl {
          url = "https://github.com/commercialhaskell/all-cabal-hashes/archive/ce857734d7d4c0fad3f6dda3a4db052836ed4619.tar.gz";
          sha256 = "sha256-Q7Zg32v5ubjVJMQXGiyyMmeFg08jTzVRKC18laiHCPE=";
        };
      };
      makeOverlayForHaskell = overlay: final: prev: {
        haskell = prev.haskell // {
          packages = prev.haskell.packages // {
            ${ghcVer} = prev.haskell.packages."${ghcVer}".override (oldArgs: {
              overrides =
                prev.lib.composeExtensions (oldArgs.overrides or (_: _: { }))
                  (overlay final prev);
            });
          };
        };
      };
      haskellBackendOverlay = makeOverlayForHaskell (final: prev: hfinal: hprev: {
        kore-rpc-types = hfinal.callCabal2nix "kore-rpc-types" ./kore-rpc-types { };
        kore = hfinal.callCabal2nix "kore" ./kore { };
        hs-backend-booster = hfinal.callCabal2nix "hs-backend-booster" ./booster { };
        hs-backend-booster-dev-tools = hfinal.callCabal2nix "hs-backend-booster-dev-tools" ./dev-tools { };
      });
      haskellBackendVersionInfoOverlay = makeOverlayForHaskell (final: prev: hfinal: hprev:
      let
        hlib = final.haskell.lib;
      in {
        kore = (hlib.overrideCabal hprev.kore (drv: {
          doCheck = false;
          postPatch = ''
            ${drv.postPatch or ""}
            substituteInPlace src/Kore/VersionInfo.hs \
              --replace '$(GitRev.gitHash)' '"${self.rev or "dirty"}"'
          '';
          # TODO: this was part of the previous flake, but can most probably be removed
          # postInstall = ''
          #   ${drv.postInstall or ""}
          # '';
        })).override {
          # bit pathological, but ghc-compact is already included with the ghc compiler
          # and depending on another copy of ghc-compact breaks HLS in the dev shell.
          ghc-compact = null;
        };
        hs-backend-booster = hlib.overrideCabal hprev.hs-backend-booster (drv: {
          doCheck = false;
          postPatch = ''
            ${drv.postPatch or ""}
            substituteInPlace library/Booster/VersionInfo.hs \
              --replace '$(GitRev.gitHash)' '"${self.rev or "dirty"}"'
          '';
        });
      });
      haskellDependenciesOverlay = makeOverlayForHaskell (final: prev: hfinal: hprev:
      let
        hlib = final.haskell.lib;
      in {
        json-rpc = hlib.markUnbroken hprev.json-rpc;
        smtlib-backends-process = hlib.markUnbroken (hlib.dontCheck hprev.smtlib-backends-process);
        decision-diagrams = hlib.markUnbroken (hlib.dontCheck hprev.decision-diagrams);
      });
      pkgs = import nixpkgs {
        inherit system;
        overlays = [
          allCabalHashesOverlay
          haskellBackendOverlay
          haskellBackendVersionInfoOverlay
          haskellDependenciesOverlay
        ];
      };
      pkgsClean = import nixpkgs {
        inherit system;
      };
      # This should based on the compiler version from the resolver in stack.yaml.
      ghcVer = "ghc965";
    in {
      packages = rec {
        default = hs-backend-booster;
        kore-rpc-types = pkgs.haskell.packages.${ghcVer}.kore-rpc-types;
        kore = pkgs.haskell.packages.${ghcVer}.kore;
        hs-backend-booster = pkgs.haskell.packages.${ghcVer}.hs-backend-booster;
        hs-backend-booster-dev-tools = pkgs.haskell.packages.${ghcVer}.hs-backend-booster-dev-tools;
      };

      # TODO: replicate style devshell
      # TODO: replicate cabal devshell
      # TODO: replicate default devshell
      # note: consider using haskellPackages.shellFor
      devShells = {
        # Separate fourmolu and cabal shells just for CI
        style = pkgsClean.mkShell {
          name = "haskell style check shell";
          packages = [

          ];
        };
        cabal = pkgs.mkShell {
          name = "haskell cabal shell";
          packages = [

          ];
        };
        default = pkgs.mkShell {
          name = "haskell default shell";
          packages = [

          ];
        };
      };
    });
}