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
    };
  };
  resolver = "lts-20.8";
  modules = [
    ({ lib, ... }: { packages = { }; })
    { packages = { "$everything" = { ghcOptions = [ "-haddock" ]; }; }; }
    ({ lib, ... }: { planned = lib.mkOverride 900 true; })
  ];
}
