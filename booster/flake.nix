{
  description = "hs-backend-booster";

  inputs = {
    k-framework.url = "github:runtimeverification/k";
    nixpkgs.follows = "haskell-nix/nixpkgs-unstable";
    haskell-nix.url = "github:input-output-hk/haskell.nix";
    haskell-backend.url = "github:runtimeverification/haskell-backend";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, haskell-nix, k-framework, haskell-backend, ... }@inputs:
    let
      inherit (nixpkgs) lib;
      perSystem = lib.genAttrs nixpkgs.lib.systems.flakeExposed;
      nixpkgsForSystem = system:
        import nixpkgs {
          inherit (haskell-nix) config;
          inherit system;
          overlays = [ haskell-nix.overlays.combined haskell-backend.overlays.z3 ];
        };
      allNixpkgsFor = perSystem nixpkgsForSystem;
      nixpkgsFor = system: allNixpkgsFor.${system};
      index-state = "2023-04-24T00:00:00Z";

      boosterBackendFor = { compiler, pkgs, profiling ? false, k }:
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
        in
        pkgs.haskell-nix.cabalProject {
          name = "hs-backend-booster";
          supportHpack = true;
          compiler-nix-name = compiler;
          src = pkgs.nix-gitignore.gitignoreSourcePure [
            ''
              /test/parser
              /test/internalisation
              /test/rpc-integration
              /scripts
              /.github
            ''
            ./.gitignore
          ] ./.;
          inherit index-state;

          shell = {
            withHoogle = true;
            tools = {
              cabal = { inherit index-state; };
              haskell-language-server = { inherit index-state; };
              fourmolu = {
                inherit index-state;
                version = "0.12.0.0";
              };
              hlint = "latest";
            };
            nativeBuildInputs = with nixpkgs.legacyPackages.${pkgs.system}; [
              nixpkgs-fmt
              hpack
              zlib
            ];
            shellHook = "rm -f *.cabal && hpack";
          };
          modules = [{
            enableProfiling = profiling;
            enableLibraryProfiling = profiling;
            packages.hs-backend-booster.components.exes.hs-booster-proxy = add-z3 "hs-booster-proxy";
            packages.hs-backend-booster.components.tests.llvm-integration = {
              build-tools = with pkgs; lib.mkForce [ makeWrapper ];
              postInstall = ''
                wrapProgram $out/bin/llvm-integration --prefix PATH : ${lib.makeBinPath [ k ]}
              '';
            };

            packages = { ghc.components.library.doHaddock = false; };
          }];
        };

      defaultCompiler = "ghc927";

      # Get flake outputs for different GHC versions
      flakesFor = pkgs: k:
        let compilers = [ defaultCompiler ];

        in builtins.listToAttrs (lib.lists.forEach compilers (compiler:
          lib.attrsets.nameValuePair compiler
          ((boosterBackendFor { inherit compiler pkgs k; }).flake { }))
          ++ lib.lists.forEach compilers (compiler:
            lib.attrsets.nameValuePair (compiler + "-prof")
            ((boosterBackendFor {
              inherit compiler pkgs k;
              profiling = true;
            }).flake { })));

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
            (compiler: flake: { "${compiler}" = flake.${attr} or { }; }) flakes;
          addPrefix = compiler:
            lib.attrsets.mapAttrs' (output: drv:
              lib.attrsets.nameValuePair "${compiler}:${output}" drv);
          withPrefixes =
            builtins.map (builtins.mapAttrs addPrefix) outputsByCompiler;
          justOutputs = builtins.concatMap builtins.attrValues withPrefixes;
        in builtins.foldl' (x: y: x // y) { } justOutputs;

    in {
      packages = perSystem (system:
        let
          inherit (flakes.${defaultCompiler}) packages;
          pkgs = nixpkgsFor system;
          flakes = flakesFor pkgs k-framework.packages.${system}.k;
        in {
          hs-backend-booster =
            packages."hs-backend-booster:exe:hs-backend-booster";
          rpc-client = packages."hs-backend-booster:exe:rpc-client";
          parsetest = packages."hs-backend-booster:exe:parsetest";
          dltest = packages."hs-backend-booster:exe:dltest";
          hs-booster-proxy = packages."hs-backend-booster:exe:hs-booster-proxy";
        } // packages // collectOutputs "packages" flakes);

      apps = perSystem (system:
        let
          inherit (flakes.${defaultCompiler}) apps;
          flakes = flakesFor (nixpkgsFor system) k-framework.packages.${system}.k;
          pkgs = nixpkgsFor system;
          scripts = pkgs.symlinkJoin {
            name = "scripts";
            paths = [ ./scripts ];
            buildInputs = [ pkgs.makeWrapper ];
            postBuild = ''
              wrapProgram $out/update-haskell-backend.sh \
                --prefix PATH : ${
                  with pkgs;
                  lib.makeBinPath [ nix gnused gnugrep jq ]
                }
            '';
          };

        in {
          hs-backend-booster = apps."hs-backend-booster:exe:hs-backend-booster";
          rpc-client = apps."hs-backend-booster:exe:rpc-client";
          parsetest = apps."hs-backend-booster:exe:parsetest";
          parsetest-binary = apps."hs-backend-booster:exe:parsetest-binary";
          dltest = apps."hs-backend-booster:exe:dltest";
          hs-booster-proxy = apps."hs-backend-booster:exe:hs-booster-proxy";
          update-haskell-backend = {
            type = "app";
            program = "${scripts}/update-haskell-backend.sh";
          };
        } // apps // collectOutputs "apps" flakes);

      # To enter a development environment for a particular GHC version, use
      # the compiler name, e.g. `nix develop .#ghc8107`
      devShells = perSystem (system:
        let flakes = flakesFor (nixpkgsFor system) k-framework.packages.${system}.k;
        in {
          default = flakes.${defaultCompiler}.devShell;
        } // lib.attrsets.mapAttrs'
        (compiler: v: lib.attrsets.nameValuePair compiler v.devShell) flakes);

      # `nix build .#hs-backend-booster:test:unit-tests`
      #
      # To run a check for a particular compiler version, prefix the derivation
      # name with the GHC version, e.g.
      #
      # `nix build .#ghc8107:hs-backend-booster:test:unit-tests`
      checks = perSystem (system:
        let flakes = flakesFor (nixpkgsFor system) k-framework.packages.${system}.k;
        in flakes.${defaultCompiler}.checks // collectOutputs "checks" flakes
        // {
          integration = with nixpkgsFor system;
            with flakes.${defaultCompiler};
            callPackage ./test/rpc-integration {
              hs-backend-booster =
                packages."hs-backend-booster:exe:hs-backend-booster";
              rpc-client = packages."hs-backend-booster:exe:rpc-client";
              inherit (k-framework.packages.${system}) k;
            };
        });

      overlays.default = lib.composeManyExtensions [
        (final: prev:
          lib.optionalAttrs (!(prev ? haskell-nix))
          (inputs.haskell-nix.overlays.combined final prev))
        (_: prev:
          let inherit ((flakesFor prev k-framework.packages.${prev.system}.k).${defaultCompiler}) packages;
          in {
            hs-backend-booster =
              packages."hs-backend-booster:exe:hs-backend-booster";
            rpc-client = packages."hs-backend-booster:exe:rpc-client";
          })
      ];

      formatter =
        perSystem (system: nixpkgs.legacyPackages.${system}.nixpkgs-fmt);

      check = perSystem (system:
        (nixpkgsFor system).runCommand "check" {
          combined = builtins.attrValues self.checks.${system}
            ++ builtins.attrValues self.packages.${system};
        } ''
          echo $combined
          touch $out
        '');

    };

  nixConfig = {
    extra-substituters =
      [ "https://cache.iog.io" "https://runtimeverification.cachix.org" ];
    extra-trusted-public-keys = [
      "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ="
      "runtimeverification.cachix.org-1:wSde8xKWzRNC2buFu4vRRwI+FiZtkI57wS1EDIhMRc4="
    ];
  };
}
