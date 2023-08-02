{ stdenv, coreutils, lib, kore-rpc-booster, rpc-client, git, k, blockchain-k-plugin, openssl, procps }:

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
        export SERVER=${kore-rpc-booster}/bin/kore-rpc-booster
        export CLIENT="${rpc-client}/bin/rpc-client"
        export PLUGIN_DIR=${blockchain-k-plugin}

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
  simplify = mkIntegrationTest { name = "simplify"; };
  get-model = mkIntegrationTest { name = "get-model"; };
  issue212 = mkIntegrationTest { name = "issue212"; };
  foundry-bug-report.tar.gz = mkIntegrationTest { name = "foundry-bug-report.tar.gz"; nativeBuildInputs = [ k openssl procps ]; };
}
