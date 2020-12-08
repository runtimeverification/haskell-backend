{
  extras = hackage:
    {
      packages = {
        "haskell-lsp" = (((hackage.haskell-lsp)."0.22.0.0").revisions).default;
        "haskell-lsp-types" = (((hackage.haskell-lsp-types)."0.22.0.0").revisions).default;
        "lsp-test" = (((hackage.lsp-test)."0.11.0.2").revisions).default;
        "ghc-check" = (((hackage.ghc-check)."0.5.0.1").revisions).default;
        "hie-bios" = (((hackage.hie-bios)."0.6.1").revisions).default;
        "Chart-diagrams" = (((hackage.Chart-diagrams)."1.9.3").revisions).default;
        "SVGFonts" = (((hackage.SVGFonts)."1.7.0.1").revisions).default;
        "diagrams" = (((hackage.diagrams)."1.4").revisions).default;
        "diagrams-svg" = (((hackage.diagrams-svg)."1.4.3").revisions).default;
        "diagrams-contrib" = (((hackage.diagrams-contrib)."1.4.4").revisions).default;
        "diagrams-core" = (((hackage.diagrams-core)."1.4.2").revisions).default;
        "diagrams-lib" = (((hackage.diagrams-lib)."1.4.3").revisions).default;
        "diagrams-postscript" = (((hackage.diagrams-postscript)."1.5").revisions).default;
        "monoid-extras" = (((hackage.monoid-extras)."0.5.1").revisions).default;
        "svg-builder" = (((hackage.svg-builder)."0.1.1").revisions).default;
        "active" = (((hackage.active)."0.2.0.14").revisions).default;
        "dual-tree" = (((hackage.dual-tree)."0.2.2.1").revisions).default;
        "force-layout" = (((hackage.force-layout)."0.4.0.6").revisions).default;
        "statestack" = (((hackage.statestack)."0.3").revisions).default;
        ghcide = ./ghcide.nix;
        };
      };
  resolver = "nightly-2020-06-19";
  modules = [
    ({ lib, ... }:
      { packages = {}; })
    { packages = { "ghcide" = { package = { ghcOptions = "-DSTACK"; }; }; }; }
    ];
  }