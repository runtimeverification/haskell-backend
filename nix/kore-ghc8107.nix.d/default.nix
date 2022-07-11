{
  extras = hackage:
    {
      packages = {
        "ghc-trace-events" = (((hackage.ghc-trace-events)."0.1.2.1").revisions).default;
        "monoidal-containers" = (((hackage.monoidal-containers)."0.6.0.1").revisions).default;
        "newtype" = (((hackage.newtype)."0.2.2.0").revisions).default;
        "sqlite-simple" = (((hackage.sqlite-simple)."0.4.18.0").revisions).default;
        "direct-sqlite" = (((hackage.direct-sqlite)."2.3.26").revisions).default;
        "witherable" = (((hackage.witherable)."0.3.5").revisions).default;
        "witherable-class" = (((hackage.witherable-class)."0").revisions).default;
        "co-log" = (((hackage.co-log)."0.4.0.1").revisions).default;
        "tasty-test-reporter" = (((hackage.tasty-test-reporter)."0.1.1.4").revisions).default;
        "junit-xml" = (((hackage.junit-xml)."0.1.0.0").revisions).default;
        "compact" = (((hackage.compact)."0.2.0.0").revisions).default;
        "decision-diagrams" = (((hackage.decision-diagrams)."0.2.0.0").revisions).default;
        "ghc-events" = (((hackage.ghc-events)."0.13.0").revisions).default;
        kore = ./kore.nix;
        eventlog2speedscope = ./.stack-to-nix.cache.0;
        pipes-ghc-events = ./.stack-to-nix.cache.1;
        pipes-sqlite-simple = ./.stack-to-nix.cache.2;
        };
      };
  resolver = "lts-18.18";
  modules = [
    ({ lib, ... }:
      { packages = {}; })
    { packages = { "$everything" = { ghcOptions = [ "-haddock" ]; }; }; }
    ({ lib, ... }:
      { planned = lib.mkOverride 900 true; })
    ];
  }