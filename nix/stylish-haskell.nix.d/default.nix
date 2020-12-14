{
  extras = hackage:
    {
      packages = {
        "haskell-src-exts" = (((hackage.haskell-src-exts)."1.23.0").revisions).default;
        stylish-haskell = ./stylish-haskell.nix;
        };
      };
  resolver = "lts-15.6";
  modules = [ ({ lib, ... }: { packages = {}; }) { packages = {}; } ];
  }