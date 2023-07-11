{ cmake, openssl, pkg-config, procps, gmp, autoconf, automake, libtool, ncurses
, jq, miller, z3, stdenv, lib, nix-gitignore, mkShell, poetry, python }:
k:
mkShell {
  packages = [
    k
    ncurses # TODO: .../lib/kframework/setenv: line 31: tput: command not found
    jq
    miller # processing test statistics
    z3
    poetry
    python
    # for evm-semantics plugin
    cmake
    openssl.dev
    pkg-config
    procps
    gmp.dev
    autoconf
    automake
    libtool
  ];

  shellHook = ''
    export NIX=1 PS1=integration-shell:$PS1
  '';
}
