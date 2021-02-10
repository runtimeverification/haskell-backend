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
        "junit-xml" = (((hackage.junit-xml)."0.1.0.0").revisions).default;
        "ghc-events" = (((hackage.ghc-events)."0.13.0").revisions).default;
        kore = ./kore.nix;
        tasty-test-reporter = ./.stack-to-nix.cache.0;
        eventlog2speedscope = ./.stack-to-nix.cache.1;
        pipes-ghc-events = ./.stack-to-nix.cache.2;
        pipes-sqlite-simple = ./.stack-to-nix.cache.3;
        };
      };
  resolver = "lts-17.2";
  modules = [ ({ lib, ... }: { packages = {}; }) { packages = {}; } ];
  }