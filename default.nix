let
  sources = import ./nix/sources.nix;
  haskell-nix = import sources."haskell.nix";
  ghcide-nix = import (sources."ghcide-nix" + "/nix") { inherit haskell-nix; };
  nixpkgs = import sources."nixpkgs" ghcide-nix;
  pkgs = nixpkgs;
  project =
    pkgs.haskell-nix.stackProject {
      src = pkgs.haskell-nix.haskellLib.cleanGit { src = ./.; };
    };
  shell = import ./shell.nix { inherit default; };
  default = {
    inherit pkgs project;
    cache = [
      pkgs.haskell-nix.haskellNixRoots
      (pkgs.haskell-nix.withInputs shell)
    ];
  };

in default
