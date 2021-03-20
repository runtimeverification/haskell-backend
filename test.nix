let
  sources = import ./nix/sources.nix;
  pinned = import sources."nixpkgs" { config = {}; overlays = []; };
in

{ pkgs ? pinned
, test ? null
}:

let
  inherit (pkgs) stdenv lib;
  inherit (pkgs) bison diffutils ncurses z3;

  ttuegel =
    let
      src = builtins.fetchGit {
        url = "https://github.com/ttuegel/nix-lib";
        rev = "66bb0ab890ff4d828a2dcfc7d5968465d0c7084f";
        ref = "main";
      };
    in import src { inherit pkgs; };

  kframework =
    let
      tag = lib.fileContents ./deps/k_release;
      url = "https://github.com/kframework/k/releases/download/${tag}/release.nix";
      args = import (builtins.fetchurl { inherit url; });
      src = pkgs.fetchgit args;
    in import src {};
  inherit (kframework) k;

  default = import ./. {};
  inherit (default) kore;
in

stdenv.mkDerivation {
  name = "kore-test";
  src = ttuegel.cleanGitSubtree { name = "kore"; src = ./.; };
  preferLocalBuild = true;
  buildInputs = [
    k kore
    ncurses  # TODO: .../lib/kframework/setenv: line 31: tput: command not found
    z3
  ];
  configurePhase = ''
    export TOP=$(pwd)
  '';
  buildFlags =
    [
      "KORE_PARSER=kore-parser"
      "KORE_EXEC=kore-exec"
      "KORE_REPL=kore-repl"
      "--output-sync"
      "test"
    ]
    ++ lib.optional (test != null) "-C ${test}"
    ;
  enableParallelBuilding = true;
  preBuild = ''
    cd test
  '';
  installPhase = ''
    runHook preInstall

    touch "$out"

    runHook postInstall
  '';
}

