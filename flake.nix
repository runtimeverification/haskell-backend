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
  outputs = { self, nixpkgs, flake-utils, haskell-nix, z3-src }:
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

      haskell-src = pkgs: pkgs.applyPatches {
        src = ./.;
        postPatch = ''
          substituteInPlace kore/src/Kore/VersionInfo.hs \
            --replace '$(GitRev.gitHash)' '"${self.rev or "dirty"}"'
        '';
      };

      projectOverlay = { shell, pkgs, src }:
        pkgs.haskell-nix.stackProject' ({
          inherit shell src;
          materialized = ./nix/kore.nix.d;
          compiler-nix-name = "ghc8107";
        });
    in {
      prelude-kore = ./src/main/kore/prelude.kore;
      project = perSystem (system:
        let
          pkgs = nixpkgsFor system;
          pkgs' = nixpkgsFor' system;
        in projectOverlay {
          inherit pkgs;
          src = haskell-src pkgs';

          shell = {
            withHoogle = true;

            exactDeps = true;

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

      flake = perSystem (system: self.project.${system}.flake { });
      packages = perSystem (system: self.flake.${system}.packages);

      apps = perSystem (system: self.flake.${system}.apps);
      devShell = perSystem (system: self.flake.${system}.devShell);

      overlay = nixpkgs.lib.composeManyExtensions [
        haskell-nix.overlay

        (final: prev: {
          haskell-backend-stackProject = projectOverlay {
            pkgs = prev;
            src = haskell-src prev;
            shell = { };
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
