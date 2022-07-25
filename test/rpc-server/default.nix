{ name, stdenv, cleanSource, python, kore-rpc }:

stdenv.mkDerivation {
  inherit name;
  src = cleanSource ./.;
  preferLocalBuild = true;
  buildInputs = [ python kore-rpc ];
  enableParallelBuilding = true;
  buildPhase = ''
    python runTests.py
  '';
  installPhase = ''
    runHook preInstall
    touch "$out"
    runHook postInstall
  '';
}