{ stdenv, coreutils, lib, booster-dev, rpc-client, git, k }:

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
        export SERVER=${booster-dev}/bin/booster-dev
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
  };
  existentials = mkIntegrationTest { name = "existentials"; };
  module-addition = mkIntegrationTest { name = "module-addition"; };
}
