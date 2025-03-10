{
  description = "K Kore Language Haskell Backend";

  inputs = {
    # pin rv-utils to a fixed version
    rv-utils.url = "github:runtimeverification/rv-nix-tools/854d4f0";
    nixpkgs.follows = "rv-utils/nixpkgs";
    z3 = {
      url = "github:Z3Prover/z3/z3-4.13.4";
      flake = false;
    };
    flake-utils.url = "github:numtide/flake-utils";
  };

  # see https://github.com/lf-/nix-lib/blob/main/examples/some-cabal-hashes/flake.nix
  outputs = { self, rv-utils, nixpkgs, z3, flake-utils }:
    let
      ghcVer = "ghc965";
      makeHaskellOverlay = overlay: final: prev: {
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

      out = system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [ self.overlays.haskell-versions self.overlays.default ];
          };
        in
        {
          packages = rec {
            default = hs-backend-booster;
            kore-rpc-types = pkgs.haskell.packages.${ghcVer}.kore-rpc-types;
            kore = pkgs.haskell.packages.${ghcVer}.kore;
            hs-backend-booster = pkgs.haskell.packages.${ghcVer}.hs-backend-booster;
            hs-backend-booster-dev-tools = pkgs.haskell.packages.${ghcVer}.hs-backend-booster-dev-tools;
          };

          devShells.default =
            let haskellPackages = pkgs.haskell.packages.${ghcVer};
            in
            haskellPackages.shellFor {
              packages = p: [ self.packages.${system}.sample ];
              withHoogle = false;
              buildInputs = with haskellPackages; [
                cabal-install
              ];
            };
        };
    in
    flake-utils.lib.eachDefaultSystem out // {
      overlays = {
        haskell-versions = makeHaskellOverlay (final: prev:
          import ./nix/some-cabal-hashes.nix {
            self = final;

            overrides = 
              let 
                hprev = prev.haskell.packages;
                hfinal = final.haskell.packages;
              in {
                # FIXME these two overrides cause an error in some-cabal-hashes.nix
                # tasty-test-reporter = 
                #     final.fetchFromGitHub {
                #       owner = "goodlyrottenapple";
                #       repo = "tasty-test-reporter";
                #       rev = "b704130545aa3925a8487bd3e92f1dd5ce0512e2";
                #       sha256 = "sha256-9CN59Im0BC3vSVhL85v5eXPYYoPbV3NAuv893tXpr/U=";
                #     };
                # profiteur =
                #     final.fetchFromGitHub {
                #       owner = "goodlyrottenapple";
                #       repo = "profiteur";
                #       rev = "7b30bbe6b2a6b72a5b4896f3a0eed5587a5bf465";
                #       sha256 = "sha256-9CN59Im0BC3vSVhL85v5eXPYYoPbV3NAuv893tXpr/U=";
                #     };

                # FIXME a jailbreak does not work either (Problem is the ansi-terminal version)
                # hfinal.tasty-test-reporter = hfinal.doJailbreak hprev.tasty-test-reporter;

                hfinal.json-rpc = final.haskell.packages.dontCheck hprev.json-rpc; # 1.0.4 marked as broken!
                hfinal.decision-diagrams = hfinal.dontCheck hprev.decision-diagrams; # build runs failing tests
              };
          });
        default = makeHaskellOverlay
          (final: prev: hfinal: hprev:
            let hlib = prev.haskell.lib; in
            {
              kore-rpc-types               = hfinal.callCabal2nix "kore-rpc-types" ./kore-rpc-types { };
              kore                         = hfinal.callCabal2nix "kore" ./kore { };
              hs-backend-booster           = hfinal.callCabal2nix "hs-backend-booster" ./booster { };
              hs-backend-booster-dev-tools = hfinal.callCabal2nix "hs-backend-booster-dev-tools" ./dev-tools { };
            });
      };
    };
}