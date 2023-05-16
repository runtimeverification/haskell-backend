{ ncurses, jq, miller, z3, stdenv, lib, nix-gitignore, mach-nix }: k:
let
  mkTest = { test ? null, passthru ? { } }:
    stdenv.mkDerivation {
      name = "kore-test";
      src = nix-gitignore.gitignoreSourcePure [ ] ./.;
      preferLocalBuild = true;
      buildInputs = [
        k
        ncurses # TODO: .../lib/kframework/setenv: line 31: tput: command not found
        jq
        miller # processing test statistics
        z3
        (mach-nix.mkPython {
          requirements = ''
            jsonrpcclient
          '';
        })
      ];
      configurePhase = ''
        export TOP=$(pwd)
      '';
      buildFlags = [
        "KORE_PARSER=kore-parser"
        "KORE_EXEC=kore-exec"
        "KORE_REPL=kore-repl"
        "--output-sync"
        "test"
      ] ++ lib.optional (test != null) "-C ${test}";
      enableParallelBuilding = true;
      installPhase = ''
        runHook preInstall

        touch "$out"

        runHook postInstall
      '';

      inherit passthru;
    };
in mkTest {
  passthru = builtins.mapAttrs (n: _: mkTest { test = n; })
    (lib.attrsets.filterAttrs (_: ty: ty == "directory")
      (builtins.readDir src));
}

