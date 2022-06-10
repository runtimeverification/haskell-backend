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

      haskell-src = { pkgs, postPatch ? "" }:
        pkgs.applyPatches {
          src = ./.;
          postPatch = ''
            substituteInPlace kore/src/Kore/VersionInfo.hs \
              --replace '$(GitRev.gitHash)' '"${self.rev or "dirty"}"'
            ${postPatch}
          '';
        };

      projectOverlay =
        { pkgs, src, shell ? { }, compiler-nix-name ? "ghc8107" }:
        let
          self = pkgs.haskell-nix.stackProject' ({
            inherit shell src compiler-nix-name;
            materialized = ./nix + "/kore-${compiler-nix-name}.nix.d";
          });
        in self // {
          rematerialize-kore = pkgs.writeShellScriptBin
            "rematerialize-kore-nix-${compiler-nix-name}" ''
              #!/bin/sh
              ${self.stack-nix.passthru.generateMaterialized} ./nix/kore-${compiler-nix-name}.nix.d
            '';
        };

      projectForGhc = { ghc, stack-yaml ? null }:
        perSystem (system:
          let
            pkgs = nixpkgsFor system;
            pkgs' = nixpkgsFor' system;
          in projectOverlay {
            inherit pkgs;
            src = haskell-src {
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

      flake = perSystem (system: self.project.${system}.flake { });
      flakeGhc9 = perSystem (system: self.projectGhc9.${system}.flake { });

      packages = perSystem (system:
        self.flake.${system}.packages // {
          rematerialize = self.project.${system}.rematerialize-kore;
          rematerializeGhc9 = self.projectGhc9.${system}.rematerialize-kore;
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
            src = haskell-src { pkgs = prev; };
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
