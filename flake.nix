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
    some-cabal-hashes-lib = {
      url = "github:lf-/nix-lib";
      flake = false;
    };
  };

  outputs = { self, rv-utils, nixpkgs, z3, flake-utils, some-cabal-hashes-lib }:
    flake-utils.lib.eachDefaultSystem (system:
    let
      z3Overlay = final: prev: {
        z3 = prev.z3.overrideAttrs (_: {
          src = z3;
          version =
          let
            release = builtins.readFile "${z3}/scripts/release.yml";
          in
            # Read the release version from scripts/release.yml
            builtins.head (builtins.match ".+ReleaseVersion: '([^']+).+" release);
        });
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
        json-rpc = hlib.dontCheck (hlib.markUnbroken hprev.json-rpc);
        smtlib-backends-process = hlib.dontCheck (hlib.markUnbroken (hlib.dontCheck hprev.smtlib-backends-process));
        decision-diagrams = hlib.dontCheck (hlib.markUnbroken (hlib.dontCheck hprev.decision-diagrams));

        # dependencies on the "wrong" version of hashable
        data-fix = hlib.doJailbreak hprev.data-fix;
        text-short = hlib.doJailbreak hprev.text-short;

        # skip some package tests (might cause issues on CI)
        crypton-x509 = hlib.dontCheck hprev.crypton-x509;
        fgl = hlib.dontCheck hprev.fgl;
        fgl-arbitrary = hlib.dontCheck hprev.fgl-arbitrary;
        graphviz = hlib.dontCheck hprev.graphviz;
        lifted-base = hlib.dontCheck hprev.lifted-base;
        prettyprinter = hlib.dontCheck hprev.prettyprinter;
        tar = hlib.dontCheck hprev.tar;

        # when overriding haskell package sources that are dependencies of cabal2nix, an infinite recursion occurs
        # as we instantiate nixpkgs a second time already anyway, we can just force cabal2nix to not use overriden dependencies, thereby completely bypassing this edgecase
        cabal2nix = pkgsClean.haskell.packages."${ghcVer}".cabal2nix;
      });
      some-cabal-hashes = import "${some-cabal-hashes-lib}/lib/some-cabal-hashes.nix";
      someCabalHashesOverlay = makeOverlayForHaskell (final: prev: some-cabal-hashes {
        self = final;
        overrides = {
          # note: fetchFromGitHub should be replaced by a flake input
          # tasty-test-reporter = final.fetchFromGitHub {
          #   owner = "goodlyrottenapple";
          #   repo = "tasty-test-reporter";
          #   rev = "b704130545aa3925a8487bd3e92f1dd5ce0512e2";
          #   sha256 = "sha256-uOQYsTecYgAKhL+DIgHLAfh2DAv+ye1JWqcQGRdpiMA=";
          # };

          # a custom older version of hashable
          hashable = "1.4.2.0";

          # custom version of tar. We would want 0.6.3.0 but the
          # currently-used nixpkgs cabal hashes don't provide that
          tar = "0.6.2.0";
        };
      });
      pkgs = import nixpkgs {
        inherit system;
        overlays = [
          z3Overlay
          haskellBackendOverlay
          haskellBackendVersionInfoOverlay
          haskellDependenciesOverlay
          someCabalHashesOverlay
        ];
      };
      pkgsClean = import nixpkgs {
        inherit system;
      };
      # ghc compiler revision
      ghcVer = "ghc965";

      withZ3 = pkgs: pkg: exe: pkgs.stdenv.mkDerivation {
        name = exe;
        phases = [ "installPhase" ];
        buildInputs = with pkgs; [ makeWrapper ];
        installPhase = ''
          mkdir -p $out/bin
          makeWrapper ${pkg}/bin/${exe} $out/bin/${exe} --prefix PATH : ${pkgs.z3}/bin
        '';
      };
    in {
      packages =
      let
        kore = pkgs.haskell.packages.${ghcVer}.kore;
        hs-backend-booster = pkgs.haskell.packages.${ghcVer}.hs-backend-booster;
        hs-backend-booster-dev-tools = pkgs.haskell.packages.${ghcVer}.hs-backend-booster-dev-tools;
      in {
        kore-exec = withZ3 pkgs kore "kore-exec";
        kore-match-disjunction = withZ3 pkgs hs-backend-booster-dev-tools "kore-match-disjunction";
        kore-parser = withZ3 pkgs hs-backend-booster-dev-tools "kore-parser";
        kore-repl = withZ3 pkgs kore "kore-repl";
        kore-rpc = withZ3 pkgs kore "kore-rpc";
        kore-rpc-booster = withZ3 pkgs hs-backend-booster "kore-rpc-booster";
        kore-rpc-client = withZ3 pkgs hs-backend-booster "kore-rpc-client";
        booster-dev = withZ3 pkgs hs-backend-booster-dev-tools "booster-dev";
        inherit (pkgs.haskell.packages."${ghcVer}") haskell-language-server;
      };

      devShells =
      let
        hlib = pkgs.haskell.lib;
        hpkgs = pkgs.haskell.packages."${ghcVer}";
        shellForPackages = p: [
          p.kore-rpc-types
          p.kore
          p.hs-backend-booster
          p.hs-backend-booster-dev-tools
        ];
      in {
        # separate fourmolu and cabal shells just for CI
        style =
        let
          hlibClean = pkgsClean.haskell.lib;
          hpkgsClean = pkgsClean.haskell.packages."${ghcVer}";
        in pkgsClean.mkShell {
          name = "haskell style check shell";
          nativeBuildInputs = [
            (hlib.justStaticExecutables hpkgs.fourmolu)
            (hlib.justStaticExecutables hpkgs.hlint)
            pkgsClean.hpack
          ];
          shellHook = ''
            hpack booster && hpack dev-tools
          '';
        };
        cabal = hpkgs.shellFor {
          name = "haskell cabal shell";
          packages = shellForPackages;
          nativeBuildInputs = [
            hpkgs.cabal-install
            pkgs.hpack
            pkgs.jq
            pkgs.nix
            pkgs.z3
            pkgs.lsof
          ];
          shellHook = ''
            hpack booster && hpack dev-tools
          '';
        };
        default = hpkgs.shellFor {
          name = "haskell default shell";
          packages = shellForPackages;
          nativeBuildInputs = [
            hpkgs.cabal-install
            hpkgs.hpack
            hpkgs.fourmolu
            hpkgs.hlint
            pkgs.haskell-language-server
            pkgs.z3
            pkgs.secp256k1
          ];
        };
      };

      overlays = {
        inherit z3Overlay;
        integration-tests = (final: prev: {
          kore-tests = final.callPackage ./nix/integration-shell.nix {
            python = final.python3.withPackages (ps:
              with ps; [
                (buildPythonPackage rec {
                  pname = "jsonrpcclient";
                  version = "4.0.3";
                  src = prev.fetchFromGitHub {
                    owner = "explodinglabs";
                    repo = pname;
                    rev = version;
                    sha256 = "sha256-xqQwqNFXatGzc4JprZY1OpdPPGgpP5/ucG/qyV/n8hw=";
                  };
                  doCheck = false;
                  format = "pyproject";
                  buildInputs = [ setuptools ];
                })
              ]
            );
          };
        });
      };

      # is required by at least https://github.com/runtimeverification/k/blob/master/flake.nix
      prelude-kore = ./src/main/kore/prelude.kore;
    });
}
