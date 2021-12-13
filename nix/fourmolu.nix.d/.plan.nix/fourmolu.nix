{ system
  , compiler
  , flags
  , pkgs
  , hsPkgs
  , pkgconfPkgs
  , errorHandler
  , config
  , ... }:
  {
    flags = { dev = false; };
    package = {
      specVersion = "1.18";
      identifier = { name = "fourmolu"; version = "0.3.0.0"; };
      license = "BSD-3-Clause";
      copyright = "";
      maintainer = "Matt Parsons <parsonsmatt@gmail.com>\nGeorge Thomas <georgefsthomas@gmail.com>";
      author = "";
      homepage = "https://github.com/parsonsmatt/fourmolu";
      url = "";
      synopsis = "A formatter for Haskell source code";
      description = "A formatter for Haskell source code.";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE.md" ];
      dataDir = ".";
      dataFiles = [
        "data/examples/declaration/annotation/*.hs"
        "data/examples/declaration/class/*.hs"
        "data/examples/declaration/data/*.hs"
        "data/examples/declaration/data/gadt/*.hs"
        "data/examples/declaration/default/*.hs"
        "data/examples/declaration/deriving/*.hs"
        "data/examples/declaration/foreign/*.hs"
        "data/examples/declaration/instance/*.hs"
        "data/examples/declaration/rewrite-rule/*.hs"
        "data/examples/declaration/role-annotation/*.hs"
        "data/examples/declaration/signature/complete/*.hs"
        "data/examples/declaration/signature/fixity/*.hs"
        "data/examples/declaration/signature/inline/*.hs"
        "data/examples/declaration/signature/minimal/*.hs"
        "data/examples/declaration/signature/pattern/*.hs"
        "data/examples/declaration/signature/set-cost-centre/*.hs"
        "data/examples/declaration/signature/specialize/*.hs"
        "data/examples/declaration/signature/type/*.hs"
        "data/examples/declaration/splice/*.hs"
        "data/examples/declaration/type-families/closed-type-family/*.hs"
        "data/examples/declaration/type-families/data-family/*.hs"
        "data/examples/declaration/type-families/type-family/*.hs"
        "data/examples/declaration/type-synonyms/*.hs"
        "data/examples/declaration/type/*.hs"
        "data/examples/declaration/value/function/*.hs"
        "data/examples/declaration/value/function/arrow/*.hs"
        "data/examples/declaration/value/function/comprehension/*.hs"
        "data/examples/declaration/value/function/do/*.hs"
        "data/examples/declaration/value/function/infix/*.hs"
        "data/examples/declaration/value/function/pattern/*.hs"
        "data/examples/declaration/value/other/*.hs"
        "data/examples/declaration/value/pattern-synonyms/*.hs"
        "data/examples/declaration/warning/*.hs"
        "data/examples/import/*.hs"
        "data/examples/module-header/*.hs"
        "data/examples/other/*.hs"
        ];
      extraSrcFiles = [];
      extraTmpFiles = [];
      extraDocFiles = [ "CHANGELOG.md" "README.md" ];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
          (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
          (hsPkgs."dlist" or (errorHandler.buildDepError "dlist"))
          (hsPkgs."exceptions" or (errorHandler.buildDepError "exceptions"))
          (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
          (hsPkgs."ghc-lib-parser" or (errorHandler.buildDepError "ghc-lib-parser"))
          (hsPkgs."HsYAML" or (errorHandler.buildDepError "HsYAML"))
          (hsPkgs."HsYAML-aeson" or (errorHandler.buildDepError "HsYAML-aeson"))
          (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
          (hsPkgs."syb" or (errorHandler.buildDepError "syb"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          ];
        buildable = true;
        modules = [
          "GHC"
          "GHC/DynFlags"
          "Ormolu"
          "Ormolu/Config"
          "Ormolu/Diff"
          "Ormolu/Exception"
          "Ormolu/Imports"
          "Ormolu/Parser"
          "Ormolu/Parser/Anns"
          "Ormolu/Parser/CommentStream"
          "Ormolu/Parser/Pragma"
          "Ormolu/Parser/Result"
          "Ormolu/Parser/Shebang"
          "Ormolu/Printer"
          "Ormolu/Printer/Combinators"
          "Ormolu/Printer/Comments"
          "Ormolu/Printer/Internal"
          "Ormolu/Printer/Meat/Common"
          "Ormolu/Printer/Meat/Declaration"
          "Ormolu/Printer/Meat/Declaration/Annotation"
          "Ormolu/Printer/Meat/Declaration/Class"
          "Ormolu/Printer/Meat/Declaration/Data"
          "Ormolu/Printer/Meat/Declaration/Default"
          "Ormolu/Printer/Meat/Declaration/Foreign"
          "Ormolu/Printer/Meat/Declaration/Instance"
          "Ormolu/Printer/Meat/Declaration/RoleAnnotation"
          "Ormolu/Printer/Meat/Declaration/Rule"
          "Ormolu/Printer/Meat/Declaration/Signature"
          "Ormolu/Printer/Meat/Declaration/Splice"
          "Ormolu/Printer/Meat/Declaration/Type"
          "Ormolu/Printer/Meat/Declaration/TypeFamily"
          "Ormolu/Printer/Meat/Declaration/Value"
          "Ormolu/Printer/Meat/Declaration/Warning"
          "Ormolu/Printer/Meat/ImportExport"
          "Ormolu/Printer/Meat/Module"
          "Ormolu/Printer/Meat/Pragma"
          "Ormolu/Printer/Meat/Type"
          "Ormolu/Printer/Operators"
          "Ormolu/Printer/SpanStream"
          "Ormolu/Processing/Common"
          "Ormolu/Processing/Cpp"
          "Ormolu/Processing/Postprocess"
          "Ormolu/Processing/Preprocess"
          "Ormolu/Utils"
          ];
        hsSourceDirs = [ "src" ];
        };
      exes = {
        "fourmolu" = {
          depends = [
            (hsPkgs."fourmolu" or (errorHandler.buildDepError "fourmolu"))
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."ghc-lib-parser" or (errorHandler.buildDepError "ghc-lib-parser"))
            (hsPkgs."gitrev" or (errorHandler.buildDepError "gitrev"))
            (hsPkgs."optparse-applicative" or (errorHandler.buildDepError "optparse-applicative"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            ];
          buildable = true;
          modules = [ "Paths_fourmolu" ];
          hsSourceDirs = [ "app" ];
          mainPath = [ "Main.hs" ] ++ [ "" ];
          };
        };
      tests = {
        "tests" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            (hsPkgs."hspec" or (errorHandler.buildDepError "hspec"))
            (hsPkgs."fourmolu" or (errorHandler.buildDepError "fourmolu"))
            (hsPkgs."path" or (errorHandler.buildDepError "path"))
            (hsPkgs."path-io" or (errorHandler.buildDepError "path-io"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            ];
          build-tools = [
            (hsPkgs.buildPackages.hspec-discover.components.exes.hspec-discover or (pkgs.buildPackages.hspec-discover or (errorHandler.buildToolDepError "hspec-discover:hspec-discover")))
            ];
          buildable = true;
          modules = [ "Ormolu/Parser/PragmaSpec" "Ormolu/PrinterSpec" ];
          hsSourceDirs = [ "tests" ];
          mainPath = [ "Spec.hs" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault ../.; }