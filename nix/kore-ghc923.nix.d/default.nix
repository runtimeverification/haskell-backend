{
  extras = hackage:
    {
      packages = {
        "ghc-trace-events" = (((hackage.ghc-trace-events)."0.1.2.1").revisions).default;
        "monoidal-containers" = (((hackage.monoidal-containers)."0.6.0.1").revisions).default;
        "newtype" = (((hackage.newtype)."0.2.2.0").revisions).default;
        "sqlite-simple" = (((hackage.sqlite-simple)."0.4.18.0").revisions).default;
        "direct-sqlite" = (((hackage.direct-sqlite)."2.3.26").revisions).default;
        "witherable" = (((hackage.witherable)."0.4.2").revisions).default;
        "witherable-class" = (((hackage.witherable-class)."0").revisions).default;
        "ghc-events" = (((hackage.ghc-events)."0.17.0.3").revisions).default;
        "tasty-test-reporter" = (((hackage.tasty-test-reporter)."0.1.1.4").revisions).default;
        "junit-xml" = (((hackage.junit-xml)."0.1.0.0").revisions).default;
        "compact" = (((hackage.compact)."0.2.0.0").revisions).default;
        "zenc" = (((hackage.zenc)."0.1.2").revisions).default;
        "json-rpc" = (((hackage.json-rpc)."1.0.4").revisions)."e6805381c86fdfc782102b1aa7e3708e89492f986c8e553d953b0fa21f790a0c";
        kore = ./kore.nix;
        co-log-core = ./.stack-to-nix.cache.0;
        co-log = ./.stack-to-nix.cache.1;
        chronos = ./.stack-to-nix.cache.2;
        contiguous = ./.stack-to-nix.cache.3;
        run-st = ./.stack-to-nix.cache.4;
        typerep-map = ./.stack-to-nix.cache.5;
        bytebuild = ./.stack-to-nix.cache.6;
        bytesmith = ./.stack-to-nix.cache.7;
        byteslice = ./.stack-to-nix.cache.8;
        zigzag = ./.stack-to-nix.cache.9;
        eventlog2speedscope = ./.stack-to-nix.cache.10;
        pipes-aeson = ./.stack-to-nix.cache.11;
        pipes-ghc-events = ./.stack-to-nix.cache.12;
        pipes-sqlite-simple = ./.stack-to-nix.cache.13;
        graphviz = ./.stack-to-nix.cache.14;
        };
      };
  resolver = "nightly-2022-06-10";
  modules = [
    ({ lib, ... }:
      { packages = {}; })
    { packages = { "$everything" = { ghcOptions = [ "-haddock" ]; }; }; }
    ({ lib, ... }:
      { planned = lib.mkOverride 900 true; })
    ];
  }