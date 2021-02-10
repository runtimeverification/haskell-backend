{
  extras = hackage:
    {
      packages = {
        "ghc-lib-parser" = (((hackage.ghc-lib-parser)."8.10.3.20201220").revisions).default;
        "ghc-lib-parser-ex" = (((hackage.ghc-lib-parser-ex)."8.10.0.17").revisions).default;
        "extra" = (((hackage.extra)."1.7.3").revisions).default;
        "apply-refact" = (((hackage.apply-refact)."0.8.2.0").revisions).default;
        "ghc-exactprint" = (((hackage.ghc-exactprint)."0.6.3.1").revisions).default;
        "optparse-applicative" = (((hackage.optparse-applicative)."0.15.1.0").revisions).default;
        hlint = ./hlint.nix;
        };
      };
  resolver = "lts-14.20";
  modules = [
    ({ lib, ... }:
      { packages = {}; })
    {
      packages = {
        "$locals" = {
          package = {
            ghcOptions = "-ddump-to-file -ddump-hi -Werror=unused-imports -Werror=unused-top-binds -Werror=orphans";
            };
          };
        };
      }
    ];
  }