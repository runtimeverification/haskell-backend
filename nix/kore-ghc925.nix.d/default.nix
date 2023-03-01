{
  extras = hackage: {
    packages = {
      "chronos" = (((hackage.chronos)."1.1.5").revisions).default;
      "co-log" = (((hackage.co-log)."0.5.0.0").revisions).default;
      "compact" = (((hackage.compact)."0.2.0.0").revisions).default;
      "decision-diagrams" =
        (((hackage.decision-diagrams)."0.2.0.0").revisions).default;
      "typerep-map" = (((hackage.typerep-map)."0.6.0.0").revisions).default;
      "monad-validate" =
        (((hackage.monad-validate)."1.2.0.0").revisions)."9850f408431098b28806dd464b6825a88a0b56c84f380d7fe0454c1df9d6f881";
      kore = ./kore.nix;
      kore-rpc-types = ./kore-rpc-types.nix;
    };
  };
  resolver = "lts-20.8";
  modules = [
    ({ lib, ... }: { packages = { }; })
    { packages = { "$everything" = { ghcOptions = [ "-haddock" ]; }; }; }
    ({ lib, ... }: { planned = lib.mkOverride 900 true; })
  ];
}
