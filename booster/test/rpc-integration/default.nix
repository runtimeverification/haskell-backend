{ stdenv, coreutils, lib, hs-backend-booster, rpc-client, git, k }:

let
  mkIntegrationTest =
    { name, nativeBuildInputs ? [ ], buildFlags ? [ ], clientArgs ? [ ] }:

    stdenv.mkDerivation {
      name = "rpc-integration-${name}";
      src = ./.;
      preferLocalBuild = true;
      nativeBuildInputs = [ git coreutils ] ++ nativeBuildInputs;

      enableParallelBuilding = true;
      buildPhase = ''
        ${lib.strings.concatMapStrings (f: ''
          export ${f}
        '') buildFlags}
        export SERVER=${hs-backend-booster}/bin/hs-backend-booster
        export CLIENT=${rpc-client}/bin/rpc-client

        patchShebangs runDirectoryTest.sh
        ./runDirectoryTest.sh test-${name} --time ${
          lib.strings.concatStringsSep " " clientArgs
        }
      '';
      installPhase = ''
        runHook preInstall
        touch "$out"
        echo "| JSON file | time |" >> $out
        echo "| --------- | ---- |" >> $out
        for time in $(ls test-${name}/*.time); do
          echo "| $time | $(cat $time) |" >> $out
        done
        runHook postInstall
      '';
    };

in {
  a-to-f = mkIntegrationTest { name = "a-to-f"; };
  imp = mkIntegrationTest {
    name = "imp";
    nativeBuildInputs = [ k ];
    buildFlags = [ "MODULE=IMP" "SERVER_OPTS='-l Rewrite'" ];
    clientArgs = [ "-O 'terminal-rules=[IMP.stop]'" ];
  };
}
