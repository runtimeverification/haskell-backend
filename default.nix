let
  sources = import ./nix/sources.nix;
  haskell-nix = import sources."haskell.nix";
  nixpkgs = import sources."nixpkgs" haskell-nix;
  pkgs = nixpkgs;
in
  pkgs.haskell-nix.stackProject {
    src = pkgs.haskell-nix.haskellLib.cleanGit { src = ./.; };
  }
