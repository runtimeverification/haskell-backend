{
  description = "hs-backend-booster";

  inputs = {
    nixpkgs.follows = "haskell-nix/nixpkgs-unstable";
    haskell-nix.url = "github:input-output-hk/haskell.nix";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, haskell-nix, ... }@inputs:
    let
      inherit (nixpkgs) lib;
      perSystem = lib.genAttrs nixpkgs.lib.systems.flakeExposed;
      nixpkgsForSystem = system: import nixpkgs {
        inherit (haskell-nix) config;
        inherit system;
        overlays = [
          haskell-nix.overlays.combined
        ];
      };
      allNixpkgsFor = perSystem nixpkgsForSystem;
      nixpkgsFor = system: allNixpkgsFor.${system};
      index-state = "2022-11-16T00:00:00Z";

      boosterBackendFor = compiler: pkgs: pkgs.haskell-nix.cabalProject {
        name = "hs-backend-booster";
        compiler-nix-name = compiler;
        src = ./.;
        inherit index-state;

        shell = {
          withHoogle = true;
          tools = {
            cabal = {
              inherit index-state;
            };
            haskell-language-server = {
              inherit index-state;
            };
            fourmolu = {
              inherit index-state;
              version = "0.8.2.0";
            };
          };
          nativeBuildInputs = with nixpkgs.legacyPackages.${pkgs.system}; [
            nixpkgs-fmt
            hpack
            zlib
          ];
          shellHook = "rm -f *.cabal && hpack";
        };
        modules = [
          {
            packages = {
              ghc.components.library.doHaddock = false;
            };
          }
        ];
      };

      defaultCompiler = "ghc924";

      # Get flake outputs for different GHC versions
      flakesFor = pkgs: builtins.listToAttrs
        (
          lib.lists.forEach [ defaultCompiler "ghc925" "ghc8107" ]
            (compiler: lib.attrsets.nameValuePair
              compiler
              ((boosterBackendFor compiler pkgs).flake { })
            )
        );

      # Takes an attribute set mapping compiler versions to `flake`s generated
      # by `haskell.nix` (see `flakesFor` above) and suffixes each derivation
      # in all flake outputs selected by `attr` with the corresponding compiler
      # version, then flattens the resulting structure to combine all derivations
      # into a single set
      #
      #    collectOutputs
      #      "checks"
      #      {
      #        ghc8107 = { checks = { x:y:z = <drv>; }; };
      #        ghc924 = { checks = { x:y:z = <drv>; }; };
      #      }
      #
      # => { ghc8107:x:y:z = <drv>; ghc924:x:y:z = <drv>; }
      collectOutputs = attr: flakes:
        let
          outputsByCompiler = lib.mapAttrsToList
            (compiler: flake: { "${compiler}" = flake.${attr} or { }; })
            flakes;
          addPrefix = compiler: lib.attrsets.mapAttrs'
            (output: drv:
              lib.attrsets.nameValuePair "${compiler}:${output}" drv
            );
          withPrefixes = builtins.map
            (builtins.mapAttrs addPrefix)
            outputsByCompiler;
          justOutputs = builtins.concatMap builtins.attrValues withPrefixes;
        in
        builtins.foldl' (x: y: x // y) { } justOutputs;

    in
    {
      packages = perSystem (system:
        let
          inherit (flakes.${defaultCompiler}) packages;
          pkgs = nixpkgsFor system;
          flakes = flakesFor pkgs;
        in
        {
          hs-backend-booster = packages."hs-backend-booster:exe:hs-backend-booster";
          rpc-client = packages."hs-backend-booster:exe:rpc-client";
        } // packages // collectOutputs "packages" flakes
      );

      apps = perSystem (system:
        let
          inherit (flakes.${defaultCompiler}) apps;
          flakes = flakesFor (nixpkgsFor system);
          pkgs = nixpkgsFor system;
        in
        {
          hs-backend-booster = apps."hs-backend-booster:exe:hs-backend-booster";
          rpc-client = apps."hs-backend-booster:exe:rpc-client";
        } // apps // collectOutputs "apps" flakes
      );

      # To enter a development environment for a particular GHC version, use
      # the compiler name, e.g. `nix develop .#ghc8107`
      devShells = perSystem (system:
        let
          flakes = flakesFor (nixpkgsFor system);
        in
        {
          default = flakes.${defaultCompiler}.devShell;
        } // lib.attrsets.mapAttrs'
          (compiler: v: lib.attrsets.nameValuePair compiler v.devShell)
          flakes
      );


      # `nix build .#hs-backend-booster:test:test-suite`
      #
      # To run a check for a particular compiler version, prefix the derivation
      # name with the GHC version, e.g.
      #
      # `nix build .#ghc8107:hs-backend-booster:test:test-suite`
      checks = perSystem (system:
        let
          flakes = flakesFor (nixpkgsFor system);
        in
        flakes.${defaultCompiler}.checks // collectOutputs "checks" flakes
      );

      overlays.default = lib.composeManyExtensions [
        (final: prev:
          # Needed to build Inferno itself
          lib.optionalAttrs (!(prev ? haskell-nix))
            (inputs.haskell-nix.overlays.combined final prev)
        )
        (_: prev:
          let
            inherit ((flakesFor prev).${defaultCompiler}) packages;
          in
          {
            hs-backend-booster = packages."hs-backend-booster:exe:hs-backend-booster";
            rpc-client = packages."hs-backend-booster:exe:rpc-client";
          }
        )
      ];

      formatter = perSystem (system: nixpkgs.legacyPackages.${system}.nixpkgs-fmt);

      check = perSystem (system:
        (nixpkgsFor system).runCommand "check"
          {
            combined = builtins.attrValues self.checks.${system}
              ++ builtins.attrValues self.packages.${system};
          }
          ''
            echo $combined
            touch $out
          ''
      );

    };


  nixConfig = {
    extra-substituters = [ "https://cache.iog.io" ];
    extra-trusted-public-keys = [
      "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ="
    ];
  };
}
