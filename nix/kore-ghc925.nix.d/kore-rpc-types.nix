{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, errorHandler, config, ...
}:
{
  flags = { };
  package = {
    specVersion = "2.2";
    identifier = {
      name = "kore-rpc-types";
      version = "0.60.0.0";
    };
    license = "BSD-3-Clause";
    copyright = "2018-2021 Runtime Verification Inc";
    maintainer = "ana.pantilie@runtimeverification.com";
    author = "Runtime Verification Inc";
    homepage = "https://github.com/runtimeverification/haskell-backend#readme";
    url = "";
    synopsis = "";
    description = "Please see the [README](README.md) file.";
    buildType = "Simple";
    isLocal = true;
    detailLevel = "FullDetails";
    licenseFiles = [ ];
    dataDir = ".";
    dataFiles = [ ];
    extraSrcFiles = [ ];
    extraTmpFiles = [ ];
    extraDocFiles = [ ];
  };
  components = {
    "library" = {
      depends = [
        (hsPkgs."base" or (errorHandler.buildDepError "base"))
        (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
        (hsPkgs."aeson-pretty" or (errorHandler.buildDepError "aeson-pretty"))
        (hsPkgs."deriving-aeson" or (errorHandler.buildDepError
          "deriving-aeson"))
        (hsPkgs."json-rpc" or (errorHandler.buildDepError "json-rpc"))
        (hsPkgs."prettyprinter" or (errorHandler.buildDepError "prettyprinter"))
        (hsPkgs."text" or (errorHandler.buildDepError "text"))
      ];
      buildable = true;
      modules = [ "Kore/JsonRpc/Types" "Kore/Syntax/Json/Types" ];
      hsSourceDirs = [ "src" ];
    };
  };
} // rec {
  src = (pkgs.lib).mkDefault ./kore-rpc-types;
}
