let
  sources = import ./nix/sources.nix;
  haskell-nix = import sources."haskell.nix";
  nixpkgs = import sources."nixpkgs" haskell-nix;
  pkgs = nixpkgs;
  default =
    pkgs.haskell-nix.stackProject {
      src = pkgs.haskell-nix.haskellLib.cleanGit { src = ./.; };
    };
in
  {
    inherit default;
    cache = [
      pkgs.haskell-nix.haskellNixRoots
      (pkgs.haskell-nix.withInputs default)
    ];
  }
