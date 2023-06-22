{ cmake, openssl, pkg-config, procps, ncurses, jq, miller, z3, stdenv, lib, nix-gitignore, mach-nix, mkShell }: k:
mkShell {
  packages = [
    k
    ncurses # TODO: .../lib/kframework/setenv: line 31: tput: command not found
    jq
    miller # processing test statistics
    z3
    (mach-nix.mkPython {
      requirements = ''
        jsonrpcclient
        poetry
      '';
    })
    # for evm-semantics plugin
    cmake
    openssl.dev
    pkg-config
    procps
  ];

  shellHook = ''
    export NIX=1 PS1=integration-shell:$PS1
  '';
}
