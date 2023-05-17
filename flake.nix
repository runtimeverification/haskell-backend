{
  description = "K Kore Language Haskell Backend";
  inputs = {
    haskell-nix.url = "github:input-output-hk/haskell.nix";
    nixpkgs.follows = "haskell-nix/nixpkgs-unstable";
    z3-src = {
      url = "github:Z3Prover/z3/z3-4.8.15";
      flake = false;
    };
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
    mach-nix.url = "github:DavHau/mach-nix";
  };
  outputs = { self, nixpkgs, haskell-nix, z3-src, mach-nix, ... }:
    let
      inherit (nixpkgs) lib;
      z3-overlay = (final: prev: {
        z3 = prev.z3.overrideAttrs (old: {
          src = z3-src;
          version =
            # hacky way of keeping the version number of this derivation consistent with
            # the z3-src input.
            let lock = builtins.fromJSON (builtins.readFile ./flake.lock);
            in builtins.replaceStrings [ "z3-" ] [ "" ]
            lock.nodes.z3-src.original.ref;
        });
      });
      integration-tests-overlay = (final: prev: {
        kore-tests = final.callPackage ./nix/integration-shell.nix { mach-nix = mach-nix.lib."${prev.system}"; };
      });
      perSystem = lib.genAttrs nixpkgs.lib.systems.flakeExposed;
      nixpkgsFor = system:
        import nixpkgs {
          inherit (haskell-nix) config;
          inherit system;
          overlays = [ haskell-nix.overlays.combined z3-overlay ];
        };

      compiler-nix-name = "ghc927";
      index-state = "2023-04-24T00:00:00Z";
      fourmolu-version = "0.12.0.0";
      hlint-version = "3.4.1";

      haskell-backend-src = pkgs:
        pkgs.applyPatches {
          name = "haskell-backend-src";
          # make sure we remove all nix files and flake.lock, since any changes to these triggers re-compilation of kore
          src = pkgs.nix-gitignore.gitignoreSourcePure [
            "./github"
            "/nix"
            "*.nix"
            "*.nix.sh"
            "/.github"
            "flake.*"
            "/profile"
            "/profile-*"
            ./.gitignore
          ] ./.;
          postPatch = ''
            substituteInPlace kore/src/Kore/VersionInfo.hs \
              --replace '$(GitRev.gitHash)' '"${self.rev or "dirty"}"'
          '';
        };

      koreFor = { pkgs, profiling ? false
        , profilingDetail ? "toplevel-functions", ghcOptions ? [ ] }:
        let
          add-z3 = exe: {
            build-tools = with pkgs; lib.mkForce [ makeWrapper ];
            postInstall = ''
              wrapProgram $out/bin/${exe} --prefix PATH : ${
                with pkgs;
                lib.makeBinPath [ z3 ]
              }
            '';
          };
        in pkgs.haskell-nix.cabalProject ({
          name = "kore";
          inherit compiler-nix-name index-state;
          src = haskell-backend-src pkgs;

          shell = {
            withHoogle = true;
            tools = {
              cabal = { inherit index-state; };
              haskell-language-server = { inherit index-state; };
              fourmolu = {
                inherit index-state;
                version = fourmolu-version;
              };
              eventlog2html = "latest";
              ghc-prof-flamegraph = "latest";
              hlint = {
                inherit index-state;
                version = hlint-version;
              };
            };
            nativeBuildInputs = with nixpkgs.legacyPackages.${pkgs.system};
              [ nixpkgs-fmt ]
              ++ lib.optional (pkgs.system == "aarch64-darwin") pkgs'.llvm_12;
          };

          modules = [{
            enableProfiling = profiling;
            enableLibraryProfiling = profiling;
            packages.kore = {
              inherit profilingDetail ghcOptions;

              # Wrap all the kore-* executables which use Z3 with
              # the path to our pinned Z3 version
              components.exes.kore-exec = add-z3 "kore-exec";
              components.exes.kore-rpc = add-z3 "kore-rpc";
              components.exes.kore-repl = add-z3 "kore-repl";
              components.exes.kore-check-functions =
                add-z3 "kore-check-functions";

              components.tests.kore-test.preCheck = ''
                # provide parser test data for json golden tests
                  mkdir -p ../test/parser
                  cp -r ${./test/parser}/* ../test/parser
                # Add Z3 to PATH for unit tests.
                  export PATH="$PATH''${PATH:+:}${lib.getBin pkgs.z3}/bin"
              '';
            };
          }];
        });
    in {
      prelude-kore = ./src/main/kore/prelude.kore;

      project = perSystem (system: koreFor { pkgs = nixpkgsFor system; });

      projectProfilingEventlog = perSystem (system:
        koreFor {
          pkgs = nixpkgsFor system;
          profiling = true;
          ghcOptions = [ "-eventlog" ];
        });

      projectEventlogInfoTable = perSystem (system:
        koreFor {
          pkgs = nixpkgsFor system;
          ghcOptions =
            [ "-finfo-table-map" "-fdistinct-constructor-tables" "-eventlog" ];
        });

      flake = perSystem (system: self.project.${system}.flake { });

      packages = perSystem (system:
        self.flake.${system}.packages // {
          kore-exec =
            self.project.${system}.hsPkgs.kore.components.exes.kore-exec;
          kore-exec-prof =
            self.projectProfilingEventlog.${system}.hsPkgs.kore.components.exes.kore-exec;
          kore-exec-infotable =
            self.projectEventlogInfoTable.${system}.hsPkgs.kore.components.exes.kore-exec;
        });

      apps = perSystem (system:
        self.flake.${system}.apps // (let
          pkgs = nixpkgsFor system;
          profiling-script = pkgs.callPackage ./nix/run-profiling.nix {
            inherit (pkgs.haskellPackages)
              hp2pretty eventlog2html;
            kore-exec =
              self.project.${system}.hsPkgs.kore.components.exes.kore-exec;
            kore-exec-prof =
              self.projectProfilingEventlog.${system}.hsPkgs.kore.components.exes.kore-exec;
            kore-exec-infotable =
              self.projectEventlogInfoTable.${system}.hsPkgs.kore.components.exes.kore-exec;
          };
          fourmolu = haskell-nix.hackage-package { name = "fourmolu"; version = fourmolu-version; inherit compiler-nix-name index-state; }.components.exes.fourmolu;
          scripts = pkgs.symlinkJoin {
            name = "fourmolu-format";
            paths = [ ./scripts ];
            buildInputs = [ pkgs.makeWrapper ];
            postBuild = ''
              wrapProgram $out/fourmolu.sh \
                --set PATH ${
                  with pkgs;
                  lib.makeBinPath [ haskellPackages.fourmolu git gnugrep findutils ]
                }
            '';
          };
        in {
          profile = {
            type = "app";
            program = "${profiling-script}/bin/run-profiling";
          };
          format = {
            type = "app";
            program = "${scripts}/fourmolu.sh";
          };
        }));

      devShells =
        perSystem (system: { default = self.flake.${system}.devShell; });

      overlay = nixpkgs.lib.composeManyExtensions [
        haskell-nix.overlay
        (final: prev: {
          haskell-backend-cabalProject = koreFor { pkgs = final; };
        })
        z3-overlay
        integration-tests-overlay
      ];
      overlays.z3 = z3-overlay;
      overlays.integration-tests = integration-tests-overlay;
    };
}
