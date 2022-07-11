{
  description = "K Kore Language Haskell Backend";
  inputs = {
    haskell-nix.url = "github:input-output-hk/haskell.nix";
    nixpkgs.follows = "haskell-nix/nixpkgs-unstable";
    z3-src = {
      url = "github:Z3Prover/z3/z3-4.8.15";
      flake = false;
    };
  };
  outputs = { self, nixpkgs, haskell-nix, z3-src }:
    let
      perSystem = nixpkgs.lib.genAttrs [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      nixpkgsFor = system:
        import nixpkgs {
          inherit system;
          overlays = [ haskell-nix.overlay ];
          inherit (haskell-nix) config;
        };
      nixpkgsFor' = system:
        import nixpkgs {
          inherit system;
          inherit (haskell-nix) config;
        };

      haskell-backend-src = { pkgs, ghc, postPatch ? "" }:
        pkgs.applyPatches {
          name = "haskell-backend-src";
          # make sure we remove all nix files and flake.lock, since any changes to these triggers re-compilation of kore
          src = pkgs.nix-gitignore.gitignoreSourcePure [
            "/nix"
            "*.nix"
            "*.nix.sh"
            "/.github"
            "flake.lock"
            ./.gitignore
          ] ./.;
          postPatch = ''
            substituteInPlace kore/src/Kore/VersionInfo.hs \
              --replace '$(GitRev.gitHash)' '"${self.rev or "dirty"}-${ghc}"'
            ${postPatch}
          '';
        };

      projectOverlay = { pkgs, src, shell ? { }, compiler-nix-name ? "ghc8107"
        , profiling ? false, profilingDetail ? "toplevel-functions"
        , ghcOptions ? [ ] }:
        let
          self = pkgs.haskell-nix.stackProject' ({
            inherit shell src compiler-nix-name;
            modules = [{
              enableLibraryProfiling = profiling;
              packages.kore = {
                enableLibraryProfiling = profiling;
                enableProfiling = profiling;
                inherit profilingDetail ghcOptions;
              };
            }];
            materialized = ./nix + "/kore-${compiler-nix-name}.nix.d";
          });
        in self // {
          rematerialize-kore = pkgs.writeShellScriptBin
            "rematerialize-kore-nix-${compiler-nix-name}" ''
              #!/bin/sh
              ${self.stack-nix.passthru.generateMaterialized} ./nix/kore-${compiler-nix-name}.nix.d
            '';
        };

      binWithFlags = { system, bin, add-flags }:
        let pkgs = nixpkgsFor' system;
        in pkgs.symlinkJoin {
          name = "${bin}-${add-flags}";
          paths = [ bin ];
          buildInputs = [ pkgs.makeWrapper ];
          postBuild = ''
            for i in "$out"/bin/*; do
              wrapProgram "$i" --add-flags "${add-flags}"
            done
          '';
        };

      projectForGhc = { ghc, stack-yaml ? null, profiling ? false
        , profilingDetail ? "toplevel-functions", ghcOptions ? [ ] }:
        perSystem (system:
          let
            pkgs = nixpkgsFor system;
            pkgs' = nixpkgsFor' system;
          in projectOverlay {
            inherit pkgs profiling ghcOptions;
            src = haskell-backend-src {
              inherit ghc;
              pkgs = pkgs';
              postPatch = if stack-yaml != null then
                "cp ${stack-yaml} stack.yaml"
              else
                "";
            };

            compiler-nix-name = ghc;
            shell = {
              # withHoogle = true;

              # exactDeps = true;

              # We use the ones from Nixpkgs, since they are cached reliably.
              # Eventually we will probably want to build these with haskell.nix.
              nativeBuildInputs = [
                pkgs'.cabal-install
                pkgs'.hlint
                pkgs'.haskellPackages.fourmolu
                pkgs'.stack
                pkgs'.nixfmt
                pkgs'.haskellPackages.eventlog2html
                pkgs'.haskellPackages.ghc-prof-flamegraph
                pkgs'.haskellPackages.hs-speedscope
              ] ++ (if system == "aarch64-darwin" then
                [ pkgs'.llvm_12 ]
              else
                [ ]);
            };
          });
    in {
      prelude-kore = ./src/main/kore/prelude.kore;

      project = projectForGhc { ghc = "ghc8107"; };
      projectGhc9 = projectForGhc {
        ghc = "ghc923";
        stack-yaml = "stack-nix-ghc9.yaml";
      };

      projectGhc9ProfilingEventlog = projectForGhc {
        ghc = "ghc923";
        stack-yaml = "stack-nix-ghc9.yaml";
        profiling = true;
        ghcOptions =
          [ "-eventlog" ];
      };

      projectGhc9ProfilingEventlogInfoTable = projectForGhc {
        ghc = "ghc923";
        stack-yaml = "stack-nix-ghc9.yaml";
        profiling = true;
        ghcOptions =
          [ "-finfo-table-map" "-fdistinct-constructor-tables" "-eventlog" ];
      };


      flake = perSystem (system: self.project.${system}.flake { });
      flakeGhc9 = perSystem (system: self.projectGhc9.${system}.flake { });

      packages = perSystem (system:
        self.flake.${system}.packages // {
          update-cabal = self.project.${system}.rematerialize-kore;
          update-cabal-ghc9 = self.projectGhc9.${system}.rematerialize-kore;

          kore-exec-prof = self.projectGhc9ProfilingEventlog.${system}.hsPkgs.kore.components.exes.kore-exec;
          kore-exec-prof-infotable = self.projectGhc9ProfilingEventlogInfoTable.${system}.hsPkgs.kore.components.exes.kore-exec;
        });

      apps = perSystem (system: self.flake.${system}.apps);

      devShells = perSystem (system: {
        default = self.flake.${system}.devShell;
        ghc9 = self.flakeGhc9.${system}.devShell;
      });
      devShell = perSystem (system: self.devShells.${system}.default);

      overlay = nixpkgs.lib.composeManyExtensions [
        haskell-nix.overlay

        (final: prev: {
          haskell-backend-stackProject = projectOverlay {
            pkgs = prev;
            src = haskell-backend-src { pkgs = prev; ghc = "ghc8107"; };
          };
        })

        (final: prev: {
          z3 = prev.z3.overrideAttrs (old: {
            src = z3-src;
            version =
              # hacky way of keeping the version number of this derivation consistent with
              # the z3-src input.
              let lock = builtins.fromJSON (builtins.readFile ./flake.lock);
              in builtins.replaceStrings [ "z3-" ] [ "" ]
              lock.nodes.z3-src.original.ref;
          });
        })
      ];
    };
}
