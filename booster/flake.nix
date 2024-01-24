{
  description = "hs-backend-booster";

  inputs = {
    haskell-backend.url = "github:runtimeverification/haskell-backend/de63565944540344cba242343500f1a61ece45c5";
    stacklock2nix.follows = "haskell-backend/stacklock2nix";
    nixpkgs.follows = "haskell-backend/nixpkgs";
  };

  outputs = { self, nixpkgs, stacklock2nix, haskell-backend }:
    let
      perSystem = nixpkgs.lib.genAttrs nixpkgs.lib.systems.flakeExposed;
      nixpkgsCleanFor = system: import nixpkgs { inherit system; };
      nixpkgsFor = system:
        import nixpkgs {
          inherit system;
          overlays =
            [ stacklock2nix.overlay self.overlay haskell-backend.overlays.z3 ];
        };
      withZ3 = pkgs: pkg: exe:
        pkgs.stdenv.mkDerivation {
          name = exe;
          phases = [ "installPhase" ];
          buildInputs = with pkgs; [ makeWrapper ];
          installPhase = ''
            mkdir -p $out/bin
            makeWrapper ${pkg}/bin/${exe} $out/bin/${exe} --prefix PATH : ${pkgs.z3}/bin
          '';
        };
    in {
      overlay = final: prev: {
        booster-backend = final.stacklock2nix {
          stackYaml = ./stack.yaml;
          # This should based on the compiler version from the resolver in stack.yaml.
          baseHaskellPkgSet = final.haskell.packages.ghc928;
          cabal2nixArgsOverrides = args:
            args // {
              # The Haskell package `"graphviz"` depends on the _system_
              # package `graphviz`, and takes the system package `graphviz` as one of its build
              # inputs, but it is actually getting passed _itself_ (not the system package
              # `graphviz`), which causes the infinite recursion.
              "graphviz" = _: { graphviz = final.graphviz; };
            };
          additionalHaskellPkgSetOverrides = hfinal: hprev:
            with final.haskell.lib; {
              decision-diagrams = dontCheck hprev.decision-diagrams;
              fgl = dontCheck hprev.fgl;
              haskeline = dontCheck hprev.haskeline;
              smtlib-backends-process = dontCheck hprev.smtlib-backends-process;
              hs-backend-booster = overrideCabal hprev.hs-backend-booster
                (drv: {
                  doCheck = false;
                  postPatch = ''
                    ${drv.postPatch or ""}
                    substituteInPlace library/Booster/VersionInfo.hs \
                      --replace '$(GitRev.gitHash)' '"${self.rev or "dirty"}"'
                  '';
                  buildTarget = "kore-rpc-booster";
                });
              json-rpc = dontCheck hprev.json-rpc;
              kore = (dontCheck hprev.kore).override {
                # bit pathological, but ghc-compact is already included with the ghc compiler
                # and depending on another copy of ghc-compact breaks HLS in the dev shell.
                ghc-compact = null;
              };
              tar = dontCheck hprev.tar;
            };
          # Additional packages that should be available for development.
          additionalDevShellNativeBuildInputs = stacklockHaskellPkgSet:
            with final; [
              haskell.packages.ghc928.cabal-install
              haskellPackages.fourmolu_0_12_0_0
              (let
                ghc-lib-parser = haskellPackages.ghc-lib-parser_9_4_5_20230430;
                ghc-lib-parser-ex =
                  haskellPackages.ghc-lib-parser-ex_9_4_0_0.override {
                    inherit ghc-lib-parser;
                  };
              in haskellPackages.hlint_3_5.override {
                inherit ghc-lib-parser ghc-lib-parser-ex;
              })
              (haskell-language-server.override {
                supportedGhcVersions = [ "928" ];
              })
              final.z3
              final.hpack
            ];
          all-cabal-hashes = final.fetchurl {
            url =
              "https://github.com/commercialhaskell/all-cabal-hashes/archive/779bc22f8c7f8e3566edd5a4922750b73a0e5ed5.tar.gz";
            sha256 = "sha256-qJ/rrdjCTil5wBlcJQ0w+1NP9F/Cr7X/pAfnnx/ahLc=";
          };
        };
      };

      packages = perSystem (system:
        let
          pkgs = nixpkgsFor system;
          hs-backend-booster = with pkgs;
            haskell.lib.justStaticExecutables
            booster-backend.pkgSet.hs-backend-booster;
        in {
          kore-rpc-booster = withZ3 pkgs hs-backend-booster "kore-rpc-booster";
        });

      devShells = perSystem (system: {
        # Separate cabal shell just for CI
        cabal = let pkgs = nixpkgsFor system;
        in pkgs.booster-backend.pkgSet.shellFor {
          packages = pkgs.booster-backend.localPkgsSelector;
          nativeBuildInputs = [
            pkgs.diffutils
            pkgs.haskell.packages.ghc928.cabal-install
            pkgs.hpack
            pkgs.jq
            pkgs.nix
            pkgs.z3
            pkgs.lsof
          ];
        };
      });

      devShell = perSystem (system:
        (nixpkgsFor system).booster-backend.devShell.overrideAttrs (old: {
          shellHook = ''
            ${old.shellHook}
            hpack && cd dev-tools && hpack
          '';
        }));
    };
}
