{
  extras = hackage: {
    packages = {
      "chronos" = (((hackage.chronos)."1.1.5").revisions).default;
      "co-log" = (((hackage.co-log)."0.5.0.0").revisions).default;
      "compact" = (((hackage.compact)."0.2.0.0").revisions).default;
      "decision-diagrams" =
        (((hackage.decision-diagrams)."0.2.0.0").revisions).default;
      "typerep-map" = (((hackage.typerep-map)."0.6.0.0").revisions).default;
      kore = ./kore.nix;
      eventlog2speedscope = ./.stack-to-nix.cache.0;
      pipes-aeson = ./.stack-to-nix.cache.1;
      pipes-ghc-events = ./.stack-to-nix.cache.2;
      pipes-sqlite-simple = ./.stack-to-nix.cache.3;
    };
  };
  resolver = "lts-20.8";
  modules = [
    ({ lib, ... }: { packages = { }; })
    { packages = { "$everything" = { ghcOptions = [ "-haddock" ]; }; }; }
    ({ lib, ... }: { planned = lib.mkOverride 900 true; })
  ];
}
