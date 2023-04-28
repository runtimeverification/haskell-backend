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
        (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
        (hsPkgs."casing" or (errorHandler.buildDepError "casing"))
        (hsPkgs."conduit" or (errorHandler.buildDepError "conduit"))
        (hsPkgs."conduit-extra" or (errorHandler.buildDepError "conduit-extra"))
        (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
        (hsPkgs."deriving-aeson" or (errorHandler.buildDepError
          "deriving-aeson"))
        (hsPkgs."json-rpc" or (errorHandler.buildDepError "json-rpc"))
        (hsPkgs."monad-logger" or (errorHandler.buildDepError "monad-logger"))
        (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
        (hsPkgs."prettyprinter" or (errorHandler.buildDepError "prettyprinter"))
        (hsPkgs."stm" or (errorHandler.buildDepError "stm"))
        (hsPkgs."stm-conduit" or (errorHandler.buildDepError "stm-conduit"))
        (hsPkgs."text" or (errorHandler.buildDepError "text"))
        (hsPkgs."unliftio" or (errorHandler.buildDepError "unliftio"))
      ];
      buildable = true;
      modules = [
        "Kore/JsonRpc/Error"
        "Kore/JsonRpc/Types"
        "Kore/JsonRpc/Types/Log"
        "Kore/JsonRpc/Server"
        "Kore/Syntax/Json/Types"
      ];
      hsSourceDirs = [ "src" ];
    };
  };
} // rec {
  src = (pkgs.lib).mkDefault ./kore-rpc-types;
}
