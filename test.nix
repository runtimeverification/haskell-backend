let
  sources = import ./nix/sources.nix;
  pinned = import sources."nixpkgs" {
    config = { };
    overlays = [ ];
  };

in { pkgs ? pinned, test ? null }:

let
  inherit (pkgs) stdenv lib;
  inherit (pkgs) bison diffutils jq miller ncurses z3;

  ttuegel = let
    src = builtins.fetchGit {
      url = "https://github.com/ttuegel/nix-lib";
      rev = "66bb0ab890ff4d828a2dcfc7d5968465d0c7084f";
      ref = "main";
    };
  in import src { inherit pkgs; };

  default = import ./. { };
  inherit (default) kore prelude-kore;

  kframework = let
    tag = lib.fileContents ./deps/k_release;
    url =
      "https://github.com/runtimeverification/k/releases/download/${tag}/release.nix";
    args = import (builtins.fetchurl { inherit url; });
    src = pkgs.fetchgit args;
  in import src { };

  k = kframework.k.override {
    haskell-backend = kore;
    inherit prelude-kore;
  };

in stdenv.mkDerivation {
  name = "kore-test";
  src = ttuegel.cleanGitSubtree {
    name = "kore";
    src = ./.;
  };
  preferLocalBuild = true;
  buildInputs = [
    k
    kore # some tests use kore-exec directly, others run through the frontend
    ncurses # TODO: .../lib/kframework/setenv: line 31: tput: command not found
    jq
    miller # processing test statistics
    z3
  ];
  configurePhase = ''
    export TOP=$(pwd)
  '';
  KORE_EXEC = "${lib.getBin kore}/bin/kore-exec";
  buildFlags = [
    "KORE_PARSER=kore-parser"
    "KORE_EXEC=kore-exec"
    "KORE_REPL=kore-repl"
    "--output-sync"
    "test"
  ] ++ lib.optional (test != null) "-C ${test}";
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

