{
  description = "hs-backend-booster";

  inputs = {
    haskell-backend.url = "github:runtimeverification/haskell-backend/a62ea52492519ef3813227796b318cfce001e3c8";
    haskell-nix.follows = "haskell-backend/haskell-nix";
    nixpkgs.follows = "haskell-backend/haskell-nix/nixpkgs-unstable";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
  };

  outputs =
    { self, nixpkgs, haskell-nix, haskell-backend, ... }@inputs:
    let
      inherit (nixpkgs) lib;
      perSystem = lib.genAttrs nixpkgs.lib.systems.flakeExposed;
      nixpkgsForSystem = system:
        import nixpkgs {
          inherit (haskell-nix) config;
          inherit system;
          overlays =
            [ haskell-nix.overlays.combined haskell-backend.overlays.z3 ];
        };
      allNixpkgsFor = perSystem nixpkgsForSystem;
      nixpkgsFor = system: allNixpkgsFor.${system};
      index-state = "2023-06-26T23:55:21Z";

      boosterBackendFor = { compiler, pkgs, profiling ? false }:
        pkgs.haskell-nix.cabalProject {
          name = "hs-backend-booster";
          supportHpack = true;
          compiler-nix-name = compiler;
          src = pkgs.applyPatches {
            name = "booster-backend-src";
            src = pkgs.nix-gitignore.gitignoreSourcePure [
              ''
                /test/parser
                /test/internalisation
                /test/rpc-integration
                /test/jsonrpc-examples
                /scripts
                /.github
              ''
              ./.gitignore
            ] ./.;
            postPatch = ''
              substituteInPlace library/Booster/VersionInfo.hs \
                --replace '$(GitRev.gitHash)' '"${self.rev or "dirty"}"'
            '';
          };
          inherit index-state;

          shell = {
            withHoogle = true;
            tools = {
              cabal = "latest";
              haskell-language-server = "latest";
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
              secp256k1
            ];
            shellHook = "rm -f *.cabal && hpack";
          };
          modules = [{
            enableProfiling = profiling;
            enableLibraryProfiling = profiling;
            packages.hs-backend-booster.components.exes.kore-rpc-booster = {
              build-tools = with pkgs; lib.mkForce [ makeWrapper ];
              postInstall = ''
                wrapProgram $out/bin/kore-rpc-booster --prefix PATH : ${
                  with pkgs;
                  lib.makeBinPath [ z3 ]
                }
              '';
            };
            packages.hs-backend-booster.components.exes.kore-rpc-dev = {
              build-tools = with pkgs; lib.mkForce [ makeWrapper ];
              postInstall = ''
                wrapProgram $out/bin/kore-rpc-dev --prefix PATH : ${
                  with pkgs;
                  lib.makeBinPath [ z3 ]
                }
              '';
            };
            packages = { ghc.components.library.doHaddock = false; };
          }];
        };

      defaultCompiler = "ghc928";

      # Get flake outputs for different GHC versions
      flakesFor = pkgs:
        let compilers = [ defaultCompiler ];

        in builtins.listToAttrs (lib.lists.forEach compilers (compiler:
          lib.attrsets.nameValuePair compiler
          ((boosterBackendFor { inherit compiler pkgs; }).flake { }))
          ++ lib.lists.forEach compilers (compiler:
            lib.attrsets.nameValuePair (compiler + "-prof")
            ((boosterBackendFor {
              inherit compiler pkgs;
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
          flakes = flakesFor pkgs;
        in {
          kore-rpc-booster = packages."hs-backend-booster:exe:kore-rpc-booster";
          booster-dev = packages."hs-backend-booster:exe:booster-dev";
          rpc-client = packages."hs-backend-booster:exe:rpc-client";
          parsetest = packages."hs-backend-booster:exe:parsetest";
        } // packages // collectOutputs "packages" flakes);

      apps = perSystem (system:
        let
          inherit (flakes.${defaultCompiler}) apps;
          flakes =
            flakesFor (nixpkgsFor system);
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
          kore-rpc-booster = apps."hs-backend-booster:exe:kore-rpc-booster";
          booster-dev = apps."hs-backend-booster:exe:booster-dev";
          rpc-client = apps."hs-backend-booster:exe:rpc-client";
          parsetest = apps."hs-backend-booster:exe:parsetest";
          parsetest-binary = apps."hs-backend-booster:exe:parsetest-binary";
          update-haskell-backend = {
            type = "app";
            program = "${scripts}/update-haskell-backend.sh";
          };
        } // apps // collectOutputs "apps" flakes);

      # To enter a development environment for a particular GHC version, use
      # the compiler name, e.g. `nix develop .#ghc8107`
      devShells = perSystem (system:
        let
          flakes =
            flakesFor (nixpkgsFor system);
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
        let
          flakes =
            flakesFor (nixpkgsFor system);
        in flakes.${defaultCompiler}.checks // collectOutputs "checks" flakes);

      overlays.default = lib.composeManyExtensions [
        (final: prev:
          lib.optionalAttrs (!(prev ? haskell-nix))
          (inputs.haskell-nix.overlays.combined final prev))
        (_: prev:
          let
            inherit (flakesFor prev) packages;
          in {
            kore-rpc-booster =
              packages."hs-backend-booster:exe:kore-rpc-booster";
            rpc-client = packages."hs-backend-booster:exe:rpc-client";
          })
      ];

      formatter =
        perSystem (system: nixpkgs.legacyPackages.${system}.nixpkgs-fmt);

    };
}
