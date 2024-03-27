{
  description = "hs-backend-booster";

  inputs = {
    haskell-backend.url = "github:runtimeverification/haskell-backend/e7ba3c7e5626d3b2dd61318e91704fd6bf47228e";
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
      ghcVersion = pkgs: pkgs.haskell.packages.ghc964;
    in {
      overlay = final: prev: {
        booster-backend = final.stacklock2nix {
          stackYaml = ./stack.yaml;
          # This should based on the compiler version from the resolver in stack.yaml.
          baseHaskellPkgSet = ghcVersion final;
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
              crypton-x509 = dontCheck hprev.crypton-x509;
              decision-diagrams = dontCheck hprev.decision-diagrams;
              fgl = dontCheck hprev.fgl;
              graphviz = dontCheck hprev.graphviz;
              smtlib-backends-process = dontCheck hprev.smtlib-backends-process;
              hs-backend-booster = overrideCabal hprev.hs-backend-booster
                (drv: {
                  doCheck = false;
                  postPatch = ''
                    ${drv.postPatch or ""}
                    substituteInPlace library/Booster/VersionInfo.hs \
                      --replace '$(GitRev.gitHash)' '"${self.rev or "dirty"}"'
                  '';
                });
              json-rpc = dontCheck hprev.json-rpc;
              kore = (dontCheck hprev.kore).override {
                # bit pathological, but ghc-compact is already included with the ghc compiler
                # and depending on another copy of ghc-compact breaks HLS in the dev shell.
                ghc-compact = null;
              };
              lifted-base = dontCheck hprev.lifted-base;
              prettyprinter = dontCheck hprev.prettyprinter;
              tar = dontCheck hprev.tar;
            };
          # Additional packages that should be available for development.
          additionalDevShellNativeBuildInputs = stacklockHaskellPkgSet:
            with ghcVersion final; [
              cabal-install
              fourmolu
              hlint
              # provides haskell-language-server-wrapper
              final.haskell-language-server
               # provides the actual haskell-language-server binary
              haskell-backend.packages.${prev.system}.haskell-language-server
              final.z3
              final.hpack
            ];
          all-cabal-hashes = final.fetchurl {
            url =
              "https://github.com/commercialhaskell/all-cabal-hashes/archive/80fe3174b98134e50d4541c9c2a3803601f6fbb7.tar.gz";
            sha256 = "sha256-b3E6JLu1tBpZnPXBJxNXfjkglY/du8k1l+WTS8Fetr4=";
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
          kore-rpc-client = withZ3 pkgs hs-backend-booster "kore-rpc-client";
        });

      devShells = perSystem (system: {
        # Separate fourmolu+hlint and cabal shells just for CI
        style = with nixpkgsCleanFor system;
          mkShell {
            nativeBuildInputs = [
              (haskell.lib.justStaticExecutables
                (ghcVersion pkgs).fourmolu)
              (haskell.lib.justStaticExecutables
                (ghcVersion pkgs).hlint)
            ];
          };
        cabal = let pkgs = nixpkgsFor system;
        in pkgs.booster-backend.pkgSet.shellFor {
          packages = pkgs.booster-backend.localPkgsSelector;
          nativeBuildInputs = [
            pkgs.diffutils
            (ghcVersion pkgs).cabal-install
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
            hpack && hpack dev-tools
          '';
        }));
    };
}
