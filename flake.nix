{
  description = "K Kore Language Haskell Backend";
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-23.05";
    stacklock2nix.url = "github:cdepillabout/stacklock2nix";
    z3 = {
      url = "github:Z3Prover/z3/z3-4.12.1";
      flake = false;
    };
  };
  outputs = { self, nixpkgs, stacklock2nix, z3 }:
    let
      perSystem = nixpkgs.lib.genAttrs nixpkgs.lib.systems.flakeExposed;
      nixpkgsCleanFor = system: import nixpkgs { inherit system; };
      nixpkgsFor = system:
        import nixpkgs {
          inherit system;
          overlays = [ stacklock2nix.overlay self.overlay self.overlays.z3 ];
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
        haskell-backend = final.stacklock2nix {
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
              json-rpc = dontCheck hprev.json-rpc;
              kore = (overrideCabal hprev.kore (drv: {
                doCheck = false;
                postPatch = ''
                  ${drv.postPatch or ""}
                  substituteInPlace src/Kore/VersionInfo.hs \
                    --replace '$(GitRev.gitHash)' '"${self.rev or "dirty"}"'
                '';
                postInstall = ''
                  ${drv.postInstall or ""}
                  rm $out/bin/kore-check-functions
                  rm $out/bin/kore-format
                '';
              })).override {
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
            ];
          all-cabal-hashes = final.fetchurl {
            url =
              "https://github.com/commercialhaskell/all-cabal-hashes/archive/779bc22f8c7f8e3566edd5a4922750b73a0e5ed5.tar.gz";
            sha256 = "sha256-qJ/rrdjCTil5wBlcJQ0w+1NP9F/Cr7X/pAfnnx/ahLc=";
          };
        };
      };

      prelude-kore = ./src/main/kore/prelude.kore;

      packages = perSystem (system:
        let
          pkgs = nixpkgsFor system;
          kore = with pkgs;
            haskell.lib.justStaticExecutables haskell-backend.pkgSet.kore;
        in {
          kore-exec = withZ3 pkgs kore "kore-exec";
          kore-match-disjunction = withZ3 pkgs kore "kore-match-disjunction";
          kore-parser = withZ3 pkgs kore "kore-parser";
          kore-repl = withZ3 pkgs kore "kore-repl";
          kore-rpc = withZ3 pkgs kore "kore-rpc";
        });

      devShells = perSystem (system: {
        # Separate fourmolu and cabal shells just for CI
        fourmolu = with nixpkgsCleanFor system;
          mkShell {
            nativeBuildInputs = [
              (haskell.lib.justStaticExecutables
                haskellPackages.fourmolu_0_12_0_0)
            ];
          };
        cabal = let pkgs = nixpkgsFor system;
        in pkgs.haskell-backend.pkgSet.shellFor {
          packages = pkgs.haskell-backend.localPkgsSelector;
          nativeBuildInputs =
            [ pkgs.haskell.packages.ghc928.cabal-install pkgs.z3 ];
        };
      });

      devShell =
        perSystem (system: (nixpkgsFor system).haskell-backend.devShell);

      overlays = {
        z3 = (final: prev: {
          z3 = prev.z3.overrideAttrs (_: {
            src = z3;
            version = let
              release = builtins.readFile "${z3}/scripts/release.yml";
              # Read the release version from scripts/release.yml
            in builtins.head
            (builtins.match ".+ReleaseVersion: '([^']+).+" release);
          });
        });
        integration-tests = (final: prev: {
          kore-tests = final.callPackage ./nix/integration-shell.nix {
            python = final.python3.withPackages (ps:
              with ps;
              [
                (buildPythonPackage rec {
                  pname = "jsonrpcclient";
                  version = "4.0.3";
                  src = prev.fetchFromGitHub {
                    owner = "explodinglabs";
                    repo = pname;
                    rev = version;
                    sha256 =
                      "sha256-xqQwqNFXatGzc4JprZY1OpdPPGgpP5/ucG/qyV/n8hw=";
                  };
                  doCheck = false;
                  format = "pyproject";
                  buildInputs = [ setuptools ];
                })
              ]);
          };
        });
      };
    };
}
