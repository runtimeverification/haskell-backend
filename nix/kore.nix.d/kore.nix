{ system
  , compiler
  , flags
  , pkgs
  , hsPkgs
  , pkgconfPkgs
  , errorHandler
  , config
  , ... }:
  ({
    flags = { release = false; threaded = true; };
    package = {
      specVersion = "2.2";
      identifier = { name = "kore"; version = "0.36.0.0"; };
      license = "NCSA";
      copyright = "2018-2020 Runtime Verification Inc";
      maintainer = "thomas.tuegel@runtimeverification.com";
      author = "Runtime Verification Inc";
      homepage = "https://github.com/kframework/kore#readme";
      url = "";
      synopsis = "";
      description = "Please see the [README](README.md) file.";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" ];
      dataDir = "data";
      dataFiles = [];
      extraSrcFiles = [ "README.md" "CHANGELOG.md" ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."adjunctions" or (errorHandler.buildDepError "adjunctions"))
          (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
          (hsPkgs."array" or (errorHandler.buildDepError "array"))
          (hsPkgs."async" or (errorHandler.buildDepError "async"))
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."clock" or (errorHandler.buildDepError "clock"))
          (hsPkgs."co-log" or (errorHandler.buildDepError "co-log"))
          (hsPkgs."comonad" or (errorHandler.buildDepError "comonad"))
          (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
          (hsPkgs."cryptonite" or (errorHandler.buildDepError "cryptonite"))
          (hsPkgs."data-default" or (errorHandler.buildDepError "data-default"))
          (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
          (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
          (hsPkgs."distributive" or (errorHandler.buildDepError "distributive"))
          (hsPkgs."errors" or (errorHandler.buildDepError "errors"))
          (hsPkgs."exceptions" or (errorHandler.buildDepError "exceptions"))
          (hsPkgs."extra" or (errorHandler.buildDepError "extra"))
          (hsPkgs."fgl" or (errorHandler.buildDepError "fgl"))
          (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
          (hsPkgs."free" or (errorHandler.buildDepError "free"))
          (hsPkgs."generic-lens" or (errorHandler.buildDepError "generic-lens"))
          (hsPkgs."generics-sop" or (errorHandler.buildDepError "generics-sop"))
          (hsPkgs."ghc-trace-events" or (errorHandler.buildDepError "ghc-trace-events"))
          (hsPkgs."gitrev" or (errorHandler.buildDepError "gitrev"))
          (hsPkgs."graphviz" or (errorHandler.buildDepError "graphviz"))
          (hsPkgs."groom" or (errorHandler.buildDepError "groom"))
          (hsPkgs."hashable" or (errorHandler.buildDepError "hashable"))
          (hsPkgs."haskeline" or (errorHandler.buildDepError "haskeline"))
          (hsPkgs."integer-gmp" or (errorHandler.buildDepError "integer-gmp"))
          (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
          (hsPkgs."logict" or (errorHandler.buildDepError "logict"))
          (hsPkgs."megaparsec" or (errorHandler.buildDepError "megaparsec"))
          (hsPkgs."memory" or (errorHandler.buildDepError "memory"))
          (hsPkgs."mmorph" or (errorHandler.buildDepError "mmorph"))
          (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
          (hsPkgs."optparse-applicative" or (errorHandler.buildDepError "optparse-applicative"))
          (hsPkgs."parser-combinators" or (errorHandler.buildDepError "parser-combinators"))
          (hsPkgs."prettyprinter" or (errorHandler.buildDepError "prettyprinter"))
          (hsPkgs."process" or (errorHandler.buildDepError "process"))
          (hsPkgs."profunctors" or (errorHandler.buildDepError "profunctors"))
          (hsPkgs."recursion-schemes" or (errorHandler.buildDepError "recursion-schemes"))
          (hsPkgs."reflection" or (errorHandler.buildDepError "reflection"))
          (hsPkgs."semialign" or (errorHandler.buildDepError "semialign"))
          (hsPkgs."sqlite-simple" or (errorHandler.buildDepError "sqlite-simple"))
          (hsPkgs."stm" or (errorHandler.buildDepError "stm"))
          (hsPkgs."streams" or (errorHandler.buildDepError "streams"))
          (hsPkgs."tar" or (errorHandler.buildDepError "tar"))
          (hsPkgs."template-haskell" or (errorHandler.buildDepError "template-haskell"))
          (hsPkgs."temporary" or (errorHandler.buildDepError "temporary"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          (hsPkgs."these" or (errorHandler.buildDepError "these"))
          (hsPkgs."time" or (errorHandler.buildDepError "time"))
          (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
          (hsPkgs."unordered-containers" or (errorHandler.buildDepError "unordered-containers"))
          (hsPkgs."vector" or (errorHandler.buildDepError "vector"))
          (hsPkgs."witherable" or (errorHandler.buildDepError "witherable"))
          (hsPkgs."zlib" or (errorHandler.buildDepError "zlib"))
          ];
        build-tools = [
          (hsPkgs.buildPackages.tasty-discover or (pkgs.buildPackages.tasty-discover or (errorHandler.buildToolDepError "tasty-discover")))
          ];
        buildable = true;
        modules = [
          "Paths_kore"
          "Changed"
          "Control/Monad/Counter"
          "Data/Graph/TopologicalSort"
          "Data/Limit"
          "Data/Sup"
          "Debug"
          "ErrorContext"
          "From"
          "Injection"
          "Kore/AST/ApplicativeKore"
          "Kore/AST/AstWithLocation"
          "Kore/AST/Common"
          "Kore/AST/Error"
          "Kore/ASTVerifier/AliasVerifier"
          "Kore/ASTVerifier/AttributesVerifier"
          "Kore/ASTVerifier/DefinitionVerifier"
          "Kore/ASTVerifier/Error"
          "Kore/ASTVerifier/ModuleVerifier"
          "Kore/ASTVerifier/PatternVerifier"
          "Kore/ASTVerifier/PatternVerifier/PatternVerifier"
          "Kore/ASTVerifier/SentenceVerifier"
          "Kore/ASTVerifier/SortVerifier"
          "Kore/ASTVerifier/Verifier"
          "Kore/Attribute/Assoc"
          "Kore/Attribute/Attributes"
          "Kore/Attribute/Axiom"
          "Kore/Attribute/Axiom/Concrete"
          "Kore/Attribute/Axiom/Constructor"
          "Kore/Attribute/Axiom/Symbolic"
          "Kore/Attribute/Axiom/Unit"
          "Kore/Attribute/Comm"
          "Kore/Attribute/Constructor"
          "Kore/Attribute/Function"
          "Kore/Attribute/Functional"
          "Kore/Attribute/Hook"
          "Kore/Attribute/Idem"
          "Kore/Attribute/Injective"
          "Kore/Attribute/Label"
          "Kore/Attribute/Location"
          "Kore/Attribute/Null"
          "Kore/Attribute/Overload"
          "Kore/Attribute/Owise"
          "Kore/Attribute/Parser"
          "Kore/Attribute/Pattern"
          "Kore/Attribute/Pattern/ConstructorLike"
          "Kore/Attribute/Pattern/Created"
          "Kore/Attribute/Pattern/Defined"
          "Kore/Attribute/Pattern/FreeVariables"
          "Kore/Attribute/Pattern/Function"
          "Kore/Attribute/Pattern/Functional"
          "Kore/Attribute/Pattern/Simplified"
          "Kore/Attribute/Priority"
          "Kore/Attribute/ProductionID"
          "Kore/Attribute/RuleIndex"
          "Kore/Attribute/Simplification"
          "Kore/Attribute/Smthook"
          "Kore/Attribute/SmtLemma"
          "Kore/Attribute/Smtlib"
          "Kore/Attribute/Smtlib/Smthook"
          "Kore/Attribute/Smtlib/Smtlib"
          "Kore/Attribute/Sort"
          "Kore/Attribute/Sort/Concat"
          "Kore/Attribute/Sort/Constructors"
          "Kore/Attribute/Sort/ConstructorsBuilder"
          "Kore/Attribute/Sort/Element"
          "Kore/Attribute/Sort/HasDomainValues"
          "Kore/Attribute/Sort/Unit"
          "Kore/Attribute/SortInjection"
          "Kore/Attribute/Source"
          "Kore/Attribute/SourceLocation"
          "Kore/Attribute/Subsort"
          "Kore/Attribute/Symbol"
          "Kore/Attribute/Symbol/Anywhere"
          "Kore/Attribute/Symbol/Klabel"
          "Kore/Attribute/Symbol/Memo"
          "Kore/Attribute/Symbol/NoEvaluators"
          "Kore/Attribute/Symbol/SymbolKywd"
          "Kore/Attribute/Synthetic"
          "Kore/Attribute/Trusted"
          "Kore/Attribute/UniqueId"
          "Kore/BugReport"
          "Kore/Builtin"
          "Kore/Builtin/AssocComm/AssocComm"
          "Kore/Builtin/AssocComm/CeilSimplifier"
          "Kore/Builtin/AssociativeCommutative"
          "Kore/Builtin/Attributes"
          "Kore/Builtin/Bool"
          "Kore/Builtin/Bool/Bool"
          "Kore/Builtin/Builtin"
          "Kore/Builtin/Encoding"
          "Kore/Builtin/Endianness"
          "Kore/Builtin/Endianness/Endianness"
          "Kore/Builtin/EqTerm"
          "Kore/Builtin/Error"
          "Kore/Builtin/External"
          "Kore/Builtin/Inj"
          "Kore/Builtin/Int"
          "Kore/Builtin/Int/Int"
          "Kore/Builtin/InternalBytes"
          "Kore/Builtin/InternalBytes/InternalBytes"
          "Kore/Builtin/KEqual"
          "Kore/Builtin/Kreflection"
          "Kore/Builtin/Krypto"
          "Kore/Builtin/List"
          "Kore/Builtin/List/List"
          "Kore/Builtin/Map"
          "Kore/Builtin/Map/Map"
          "Kore/Builtin/Set"
          "Kore/Builtin/Set/Set"
          "Kore/Builtin/Signedness"
          "Kore/Builtin/Signedness/Signedness"
          "Kore/Builtin/String"
          "Kore/Builtin/String/String"
          "Kore/Builtin/Symbols"
          "Kore/Builtin/Verifiers"
          "Kore/Debug"
          "Kore/Domain/Builtin"
          "Kore/Equation"
          "Kore/Equation/Application"
          "Kore/Equation/Equation"
          "Kore/Equation/Registry"
          "Kore/Equation/Sentence"
          "Kore/Equation/Simplification"
          "Kore/Error"
          "Kore/Exec"
          "Kore/IndexedModule/Error"
          "Kore/IndexedModule/IndexedModule"
          "Kore/IndexedModule/MetadataTools"
          "Kore/IndexedModule/MetadataToolsBuilder"
          "Kore/IndexedModule/OverloadGraph"
          "Kore/IndexedModule/Resolvers"
          "Kore/IndexedModule/SortGraph"
          "Kore/Internal/Alias"
          "Kore/Internal/ApplicationSorts"
          "Kore/Internal/Condition"
          "Kore/Internal/Conditional"
          "Kore/Internal/Inj"
          "Kore/Internal/InternalBool"
          "Kore/Internal/InternalBytes"
          "Kore/Internal/InternalInt"
          "Kore/Internal/InternalList"
          "Kore/Internal/InternalString"
          "Kore/Internal/MultiAnd"
          "Kore/Internal/MultiOr"
          "Kore/Internal/OrCondition"
          "Kore/Internal/OrPattern"
          "Kore/Internal/Pattern"
          "Kore/Internal/Predicate"
          "Kore/Internal/SideCondition"
          "Kore/Internal/SideCondition/SideCondition"
          "Kore/Internal/Substitution"
          "Kore/Internal/Symbol"
          "Kore/Internal/TermLike"
          "Kore/Internal/TermLike/Renaming"
          "Kore/Internal/TermLike/TermLike"
          "Kore/Internal/Variable"
          "Kore/Log"
          "Kore/Log/DebugAppliedRewriteRules"
          "Kore/Log/DebugClaimState"
          "Kore/Log/DebugEvaluateCondition"
          "Kore/Log/DebugProven"
          "Kore/Log/DebugSolver"
          "Kore/Log/DebugSubstitutionSimplifier"
          "Kore/Log/DebugUnification"
          "Kore/Log/ErrorBottomTotalFunction"
          "Kore/Log/ErrorDecidePredicateUnknown"
          "Kore/Log/ErrorException"
          "Kore/Log/ErrorParse"
          "Kore/Log/ErrorRewriteLoop"
          "Kore/Log/ErrorRewritesInstantiation"
          "Kore/Log/ErrorRuleMergeDuplicate"
          "Kore/Log/ErrorVerify"
          "Kore/Log/InfoAttemptUnification"
          "Kore/Log/InfoExecBreadth"
          "Kore/Log/InfoExecDepth"
          "Kore/Log/InfoProofDepth"
          "Kore/Log/InfoReachability"
          "Kore/Log/KoreLogOptions"
          "Kore/Log/Registry"
          "Kore/Log/SQLite"
          "Kore/Log/WarnFunctionWithoutEvaluators"
          "Kore/Log/WarnIfLowProductivity"
          "Kore/Log/WarnRetrySolverQuery"
          "Kore/Log/WarnStuckClaimState"
          "Kore/Log/WarnSymbolSMTRepresentation"
          "Kore/Log/WarnTrivialClaim"
          "Kore/ModelChecker/Bounded"
          "Kore/ModelChecker/Simplification"
          "Kore/ModelChecker/Step"
          "Kore/Options"
          "Kore/Parser"
          "Kore/Parser/CString"
          "Kore/Parser/Lexer"
          "Kore/Parser/Parser"
          "Kore/Parser/ParserUtils"
          "Kore/Reachability"
          "Kore/Reachability/AllPathClaim"
          "Kore/Reachability/Claim"
          "Kore/Reachability/ClaimState"
          "Kore/Reachability/OnePathClaim"
          "Kore/Reachability/Prim"
          "Kore/Reachability/Prove"
          "Kore/Reachability/SomeClaim"
          "Kore/Repl"
          "Kore/Repl/Data"
          "Kore/Repl/Interpreter"
          "Kore/Repl/Parser"
          "Kore/Repl/State"
          "Kore/Rewriting/RewritingVariable"
          "Kore/Rewriting/UnifyingRule"
          "Kore/Sort"
          "Kore/Step"
          "Kore/Step/AntiLeft"
          "Kore/Step/Axiom/EvaluationStrategy"
          "Kore/Step/Axiom/Identifier"
          "Kore/Step/Axiom/Matcher"
          "Kore/Step/Axiom/Registry"
          "Kore/Step/AxiomPattern"
          "Kore/Step/ClaimPattern"
          "Kore/Step/Function/Evaluator"
          "Kore/Step/Function/Memo"
          "Kore/Step/Implication"
          "Kore/Step/Remainder"
          "Kore/Step/Result"
          "Kore/Step/RewriteStep"
          "Kore/Step/Rule"
          "Kore/Step/Rule/Combine"
          "Kore/Step/Rule/Expand"
          "Kore/Step/Rule/Simplify"
          "Kore/Step/RulePattern"
          "Kore/Step/Search"
          "Kore/Step/Simplification/And"
          "Kore/Step/Simplification/AndPredicates"
          "Kore/Step/Simplification/AndTerms"
          "Kore/Step/Simplification/Application"
          "Kore/Step/Simplification/Bottom"
          "Kore/Step/Simplification/Builtin"
          "Kore/Step/Simplification/Ceil"
          "Kore/Step/Simplification/CeilSimplifier"
          "Kore/Step/Simplification/Condition"
          "Kore/Step/Simplification/Data"
          "Kore/Step/Simplification/Defined"
          "Kore/Step/Simplification/DomainValue"
          "Kore/Step/Simplification/Equals"
          "Kore/Step/Simplification/Exists"
          "Kore/Step/Simplification/ExpandAlias"
          "Kore/Step/Simplification/Floor"
          "Kore/Step/Simplification/Forall"
          "Kore/Step/Simplification/Iff"
          "Kore/Step/Simplification/Implies"
          "Kore/Step/Simplification/In"
          "Kore/Step/Simplification/Inhabitant"
          "Kore/Step/Simplification/Inj"
          "Kore/Step/Simplification/InjSimplifier"
          "Kore/Step/Simplification/InternalBool"
          "Kore/Step/Simplification/InternalBytes"
          "Kore/Step/Simplification/InternalInt"
          "Kore/Step/Simplification/InternalList"
          "Kore/Step/Simplification/InternalString"
          "Kore/Step/Simplification/Mu"
          "Kore/Step/Simplification/Next"
          "Kore/Step/Simplification/NoConfusion"
          "Kore/Step/Simplification/Not"
          "Kore/Step/Simplification/NotSimplifier"
          "Kore/Step/Simplification/Nu"
          "Kore/Step/Simplification/Or"
          "Kore/Step/Simplification/OrPattern"
          "Kore/Step/Simplification/Overloading"
          "Kore/Step/Simplification/OverloadSimplifier"
          "Kore/Step/Simplification/Pattern"
          "Kore/Step/Simplification/Rewrites"
          "Kore/Step/Simplification/Rule"
          "Kore/Step/Simplification/SetVariable"
          "Kore/Step/Simplification/SimplificationType"
          "Kore/Step/Simplification/Simplify"
          "Kore/Step/Simplification/StringLiteral"
          "Kore/Step/Simplification/SubstitutionSimplifier"
          "Kore/Step/Simplification/TermLike"
          "Kore/Step/Simplification/Top"
          "Kore/Step/Simplification/Variable"
          "Kore/Step/SMT/AST"
          "Kore/Step/SMT/Declaration/All"
          "Kore/Step/SMT/Declaration/Sorts"
          "Kore/Step/SMT/Declaration/Symbols"
          "Kore/Step/SMT/Encoder"
          "Kore/Step/SMT/Evaluator"
          "Kore/Step/SMT/Lemma"
          "Kore/Step/SMT/Representation/All"
          "Kore/Step/SMT/Representation/Resolve"
          "Kore/Step/SMT/Representation/Sorts"
          "Kore/Step/SMT/Representation/Symbols"
          "Kore/Step/SMT/Resolvers"
          "Kore/Step/SMT/Translate"
          "Kore/Step/Step"
          "Kore/Step/Strategy"
          "Kore/Step/Substitution"
          "Kore/Step/Transition"
          "Kore/Substitute"
          "Kore/Syntax"
          "Kore/Syntax/And"
          "Kore/Syntax/Application"
          "Kore/Syntax/Bottom"
          "Kore/Syntax/Ceil"
          "Kore/Syntax/Definition"
          "Kore/Syntax/DomainValue"
          "Kore/Syntax/Equals"
          "Kore/Syntax/Exists"
          "Kore/Syntax/Floor"
          "Kore/Syntax/Forall"
          "Kore/Syntax/Id"
          "Kore/Syntax/Iff"
          "Kore/Syntax/Implies"
          "Kore/Syntax/In"
          "Kore/Syntax/Inhabitant"
          "Kore/Syntax/Module"
          "Kore/Syntax/Mu"
          "Kore/Syntax/Next"
          "Kore/Syntax/Not"
          "Kore/Syntax/Nu"
          "Kore/Syntax/Or"
          "Kore/Syntax/Pattern"
          "Kore/Syntax/PatternF"
          "Kore/Syntax/Rewrites"
          "Kore/Syntax/Sentence"
          "Kore/Syntax/StringLiteral"
          "Kore/Syntax/Top"
          "Kore/Syntax/Variable"
          "Kore/TopBottom"
          "Kore/Unification/Procedure"
          "Kore/Unification/SubstitutionNormalization"
          "Kore/Unification/SubstitutionSimplifier"
          "Kore/Unification/UnificationProcedure"
          "Kore/Unification/UnifierT"
          "Kore/Unification/Unify"
          "Kore/Unparser"
          "Kore/Variables/Binding"
          "Kore/Variables/Free"
          "Kore/Variables/Fresh"
          "Kore/Variables/Target"
          "Kore/Verified"
          "Log"
          "Log/Entry"
          "Logic"
          "Options/SMT"
          "Pair"
          "Prelude/Kore"
          "Pretty"
          "Prof"
          "SMT"
          "SMT/AST"
          "SMT/SimpleSMT"
          "SQL"
          "SQL/ColumnDef"
          "SQL/Key"
          "SQL/Query"
          "SQL/SOP"
          "SQL/SQL"
          "Stats"
          ];
        hsSourceDirs = [ "src" ];
        };
      exes = {
        "kore-exec" = {
          depends = [
            (hsPkgs."adjunctions" or (errorHandler.buildDepError "adjunctions"))
            (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
            (hsPkgs."array" or (errorHandler.buildDepError "array"))
            (hsPkgs."async" or (errorHandler.buildDepError "async"))
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."clock" or (errorHandler.buildDepError "clock"))
            (hsPkgs."co-log" or (errorHandler.buildDepError "co-log"))
            (hsPkgs."comonad" or (errorHandler.buildDepError "comonad"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."cryptonite" or (errorHandler.buildDepError "cryptonite"))
            (hsPkgs."data-default" or (errorHandler.buildDepError "data-default"))
            (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."distributive" or (errorHandler.buildDepError "distributive"))
            (hsPkgs."errors" or (errorHandler.buildDepError "errors"))
            (hsPkgs."exceptions" or (errorHandler.buildDepError "exceptions"))
            (hsPkgs."extra" or (errorHandler.buildDepError "extra"))
            (hsPkgs."fgl" or (errorHandler.buildDepError "fgl"))
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            (hsPkgs."free" or (errorHandler.buildDepError "free"))
            (hsPkgs."generic-lens" or (errorHandler.buildDepError "generic-lens"))
            (hsPkgs."generics-sop" or (errorHandler.buildDepError "generics-sop"))
            (hsPkgs."ghc-trace-events" or (errorHandler.buildDepError "ghc-trace-events"))
            (hsPkgs."gitrev" or (errorHandler.buildDepError "gitrev"))
            (hsPkgs."graphviz" or (errorHandler.buildDepError "graphviz"))
            (hsPkgs."groom" or (errorHandler.buildDepError "groom"))
            (hsPkgs."hashable" or (errorHandler.buildDepError "hashable"))
            (hsPkgs."haskeline" or (errorHandler.buildDepError "haskeline"))
            (hsPkgs."integer-gmp" or (errorHandler.buildDepError "integer-gmp"))
            (hsPkgs."kore" or (errorHandler.buildDepError "kore"))
            (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
            (hsPkgs."logict" or (errorHandler.buildDepError "logict"))
            (hsPkgs."megaparsec" or (errorHandler.buildDepError "megaparsec"))
            (hsPkgs."memory" or (errorHandler.buildDepError "memory"))
            (hsPkgs."mmorph" or (errorHandler.buildDepError "mmorph"))
            (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
            (hsPkgs."optparse-applicative" or (errorHandler.buildDepError "optparse-applicative"))
            (hsPkgs."parser-combinators" or (errorHandler.buildDepError "parser-combinators"))
            (hsPkgs."prettyprinter" or (errorHandler.buildDepError "prettyprinter"))
            (hsPkgs."process" or (errorHandler.buildDepError "process"))
            (hsPkgs."profunctors" or (errorHandler.buildDepError "profunctors"))
            (hsPkgs."recursion-schemes" or (errorHandler.buildDepError "recursion-schemes"))
            (hsPkgs."reflection" or (errorHandler.buildDepError "reflection"))
            (hsPkgs."semialign" or (errorHandler.buildDepError "semialign"))
            (hsPkgs."sqlite-simple" or (errorHandler.buildDepError "sqlite-simple"))
            (hsPkgs."stm" or (errorHandler.buildDepError "stm"))
            (hsPkgs."streams" or (errorHandler.buildDepError "streams"))
            (hsPkgs."tar" or (errorHandler.buildDepError "tar"))
            (hsPkgs."template-haskell" or (errorHandler.buildDepError "template-haskell"))
            (hsPkgs."temporary" or (errorHandler.buildDepError "temporary"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."these" or (errorHandler.buildDepError "these"))
            (hsPkgs."time" or (errorHandler.buildDepError "time"))
            (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
            (hsPkgs."unordered-containers" or (errorHandler.buildDepError "unordered-containers"))
            (hsPkgs."vector" or (errorHandler.buildDepError "vector"))
            (hsPkgs."witherable" or (errorHandler.buildDepError "witherable"))
            (hsPkgs."zlib" or (errorHandler.buildDepError "zlib"))
            ];
          build-tools = [
            (hsPkgs.buildPackages.tasty-discover or (pkgs.buildPackages.tasty-discover or (errorHandler.buildToolDepError "tasty-discover")))
            ];
          buildable = true;
          modules = [ "GlobalMain" "Paths_kore" ];
          hsSourceDirs = [ "app/exec" "app/share" ];
          mainPath = ([
            "Main.hs"
            ] ++ (pkgs.lib).optional (!flags.release) "") ++ [ "" ];
          };
        "kore-format" = {
          depends = [
            (hsPkgs."adjunctions" or (errorHandler.buildDepError "adjunctions"))
            (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
            (hsPkgs."array" or (errorHandler.buildDepError "array"))
            (hsPkgs."async" or (errorHandler.buildDepError "async"))
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."clock" or (errorHandler.buildDepError "clock"))
            (hsPkgs."co-log" or (errorHandler.buildDepError "co-log"))
            (hsPkgs."comonad" or (errorHandler.buildDepError "comonad"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."cryptonite" or (errorHandler.buildDepError "cryptonite"))
            (hsPkgs."data-default" or (errorHandler.buildDepError "data-default"))
            (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."distributive" or (errorHandler.buildDepError "distributive"))
            (hsPkgs."errors" or (errorHandler.buildDepError "errors"))
            (hsPkgs."exceptions" or (errorHandler.buildDepError "exceptions"))
            (hsPkgs."extra" or (errorHandler.buildDepError "extra"))
            (hsPkgs."fgl" or (errorHandler.buildDepError "fgl"))
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            (hsPkgs."free" or (errorHandler.buildDepError "free"))
            (hsPkgs."generic-lens" or (errorHandler.buildDepError "generic-lens"))
            (hsPkgs."generics-sop" or (errorHandler.buildDepError "generics-sop"))
            (hsPkgs."ghc-trace-events" or (errorHandler.buildDepError "ghc-trace-events"))
            (hsPkgs."gitrev" or (errorHandler.buildDepError "gitrev"))
            (hsPkgs."graphviz" or (errorHandler.buildDepError "graphviz"))
            (hsPkgs."groom" or (errorHandler.buildDepError "groom"))
            (hsPkgs."hashable" or (errorHandler.buildDepError "hashable"))
            (hsPkgs."haskeline" or (errorHandler.buildDepError "haskeline"))
            (hsPkgs."integer-gmp" or (errorHandler.buildDepError "integer-gmp"))
            (hsPkgs."kore" or (errorHandler.buildDepError "kore"))
            (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
            (hsPkgs."logict" or (errorHandler.buildDepError "logict"))
            (hsPkgs."megaparsec" or (errorHandler.buildDepError "megaparsec"))
            (hsPkgs."memory" or (errorHandler.buildDepError "memory"))
            (hsPkgs."mmorph" or (errorHandler.buildDepError "mmorph"))
            (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
            (hsPkgs."optparse-applicative" or (errorHandler.buildDepError "optparse-applicative"))
            (hsPkgs."parser-combinators" or (errorHandler.buildDepError "parser-combinators"))
            (hsPkgs."prettyprinter" or (errorHandler.buildDepError "prettyprinter"))
            (hsPkgs."process" or (errorHandler.buildDepError "process"))
            (hsPkgs."profunctors" or (errorHandler.buildDepError "profunctors"))
            (hsPkgs."recursion-schemes" or (errorHandler.buildDepError "recursion-schemes"))
            (hsPkgs."reflection" or (errorHandler.buildDepError "reflection"))
            (hsPkgs."semialign" or (errorHandler.buildDepError "semialign"))
            (hsPkgs."sqlite-simple" or (errorHandler.buildDepError "sqlite-simple"))
            (hsPkgs."stm" or (errorHandler.buildDepError "stm"))
            (hsPkgs."streams" or (errorHandler.buildDepError "streams"))
            (hsPkgs."tar" or (errorHandler.buildDepError "tar"))
            (hsPkgs."template-haskell" or (errorHandler.buildDepError "template-haskell"))
            (hsPkgs."temporary" or (errorHandler.buildDepError "temporary"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."these" or (errorHandler.buildDepError "these"))
            (hsPkgs."time" or (errorHandler.buildDepError "time"))
            (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
            (hsPkgs."unordered-containers" or (errorHandler.buildDepError "unordered-containers"))
            (hsPkgs."vector" or (errorHandler.buildDepError "vector"))
            (hsPkgs."witherable" or (errorHandler.buildDepError "witherable"))
            (hsPkgs."zlib" or (errorHandler.buildDepError "zlib"))
            ];
          build-tools = [
            (hsPkgs.buildPackages.tasty-discover or (pkgs.buildPackages.tasty-discover or (errorHandler.buildToolDepError "tasty-discover")))
            ];
          buildable = true;
          modules = [ "GlobalMain" "Paths_kore" ];
          hsSourceDirs = [ "app/format" "app/share" ];
          mainPath = ([
            "Main.hs"
            ] ++ (pkgs.lib).optional (!flags.release) "") ++ [ "" ];
          };
        "kore-parser" = {
          depends = [
            (hsPkgs."adjunctions" or (errorHandler.buildDepError "adjunctions"))
            (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
            (hsPkgs."array" or (errorHandler.buildDepError "array"))
            (hsPkgs."async" or (errorHandler.buildDepError "async"))
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."clock" or (errorHandler.buildDepError "clock"))
            (hsPkgs."co-log" or (errorHandler.buildDepError "co-log"))
            (hsPkgs."comonad" or (errorHandler.buildDepError "comonad"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."cryptonite" or (errorHandler.buildDepError "cryptonite"))
            (hsPkgs."data-default" or (errorHandler.buildDepError "data-default"))
            (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."distributive" or (errorHandler.buildDepError "distributive"))
            (hsPkgs."errors" or (errorHandler.buildDepError "errors"))
            (hsPkgs."exceptions" or (errorHandler.buildDepError "exceptions"))
            (hsPkgs."extra" or (errorHandler.buildDepError "extra"))
            (hsPkgs."fgl" or (errorHandler.buildDepError "fgl"))
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            (hsPkgs."free" or (errorHandler.buildDepError "free"))
            (hsPkgs."generic-lens" or (errorHandler.buildDepError "generic-lens"))
            (hsPkgs."generics-sop" or (errorHandler.buildDepError "generics-sop"))
            (hsPkgs."ghc-trace-events" or (errorHandler.buildDepError "ghc-trace-events"))
            (hsPkgs."gitrev" or (errorHandler.buildDepError "gitrev"))
            (hsPkgs."graphviz" or (errorHandler.buildDepError "graphviz"))
            (hsPkgs."groom" or (errorHandler.buildDepError "groom"))
            (hsPkgs."hashable" or (errorHandler.buildDepError "hashable"))
            (hsPkgs."haskeline" or (errorHandler.buildDepError "haskeline"))
            (hsPkgs."integer-gmp" or (errorHandler.buildDepError "integer-gmp"))
            (hsPkgs."kore" or (errorHandler.buildDepError "kore"))
            (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
            (hsPkgs."logict" or (errorHandler.buildDepError "logict"))
            (hsPkgs."megaparsec" or (errorHandler.buildDepError "megaparsec"))
            (hsPkgs."memory" or (errorHandler.buildDepError "memory"))
            (hsPkgs."mmorph" or (errorHandler.buildDepError "mmorph"))
            (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
            (hsPkgs."optparse-applicative" or (errorHandler.buildDepError "optparse-applicative"))
            (hsPkgs."parser-combinators" or (errorHandler.buildDepError "parser-combinators"))
            (hsPkgs."prettyprinter" or (errorHandler.buildDepError "prettyprinter"))
            (hsPkgs."process" or (errorHandler.buildDepError "process"))
            (hsPkgs."profunctors" or (errorHandler.buildDepError "profunctors"))
            (hsPkgs."recursion-schemes" or (errorHandler.buildDepError "recursion-schemes"))
            (hsPkgs."reflection" or (errorHandler.buildDepError "reflection"))
            (hsPkgs."semialign" or (errorHandler.buildDepError "semialign"))
            (hsPkgs."sqlite-simple" or (errorHandler.buildDepError "sqlite-simple"))
            (hsPkgs."stm" or (errorHandler.buildDepError "stm"))
            (hsPkgs."streams" or (errorHandler.buildDepError "streams"))
            (hsPkgs."tar" or (errorHandler.buildDepError "tar"))
            (hsPkgs."template-haskell" or (errorHandler.buildDepError "template-haskell"))
            (hsPkgs."temporary" or (errorHandler.buildDepError "temporary"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."these" or (errorHandler.buildDepError "these"))
            (hsPkgs."time" or (errorHandler.buildDepError "time"))
            (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
            (hsPkgs."unordered-containers" or (errorHandler.buildDepError "unordered-containers"))
            (hsPkgs."vector" or (errorHandler.buildDepError "vector"))
            (hsPkgs."witherable" or (errorHandler.buildDepError "witherable"))
            (hsPkgs."zlib" or (errorHandler.buildDepError "zlib"))
            ];
          build-tools = [
            (hsPkgs.buildPackages.tasty-discover or (pkgs.buildPackages.tasty-discover or (errorHandler.buildToolDepError "tasty-discover")))
            ];
          buildable = true;
          modules = [ "GlobalMain" "Paths_kore" ];
          hsSourceDirs = [ "app/parser" "app/share" ];
          mainPath = ([
            "Main.hs"
            ] ++ (pkgs.lib).optional (!flags.release) "") ++ [ "" ];
          };
        "kore-prof" = {
          depends = [
            (hsPkgs."adjunctions" or (errorHandler.buildDepError "adjunctions"))
            (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
            (hsPkgs."array" or (errorHandler.buildDepError "array"))
            (hsPkgs."async" or (errorHandler.buildDepError "async"))
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."clock" or (errorHandler.buildDepError "clock"))
            (hsPkgs."co-log" or (errorHandler.buildDepError "co-log"))
            (hsPkgs."comonad" or (errorHandler.buildDepError "comonad"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."cryptonite" or (errorHandler.buildDepError "cryptonite"))
            (hsPkgs."data-default" or (errorHandler.buildDepError "data-default"))
            (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."distributive" or (errorHandler.buildDepError "distributive"))
            (hsPkgs."errors" or (errorHandler.buildDepError "errors"))
            (hsPkgs."eventlog2speedscope" or (errorHandler.buildDepError "eventlog2speedscope"))
            (hsPkgs."exceptions" or (errorHandler.buildDepError "exceptions"))
            (hsPkgs."extra" or (errorHandler.buildDepError "extra"))
            (hsPkgs."fgl" or (errorHandler.buildDepError "fgl"))
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            (hsPkgs."free" or (errorHandler.buildDepError "free"))
            (hsPkgs."generic-lens" or (errorHandler.buildDepError "generic-lens"))
            (hsPkgs."generics-sop" or (errorHandler.buildDepError "generics-sop"))
            (hsPkgs."ghc-trace-events" or (errorHandler.buildDepError "ghc-trace-events"))
            (hsPkgs."gitrev" or (errorHandler.buildDepError "gitrev"))
            (hsPkgs."graphviz" or (errorHandler.buildDepError "graphviz"))
            (hsPkgs."groom" or (errorHandler.buildDepError "groom"))
            (hsPkgs."hashable" or (errorHandler.buildDepError "hashable"))
            (hsPkgs."haskeline" or (errorHandler.buildDepError "haskeline"))
            (hsPkgs."integer-gmp" or (errorHandler.buildDepError "integer-gmp"))
            (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
            (hsPkgs."logict" or (errorHandler.buildDepError "logict"))
            (hsPkgs."megaparsec" or (errorHandler.buildDepError "megaparsec"))
            (hsPkgs."memory" or (errorHandler.buildDepError "memory"))
            (hsPkgs."mmorph" or (errorHandler.buildDepError "mmorph"))
            (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
            (hsPkgs."optparse-applicative" or (errorHandler.buildDepError "optparse-applicative"))
            (hsPkgs."parser-combinators" or (errorHandler.buildDepError "parser-combinators"))
            (hsPkgs."prettyprinter" or (errorHandler.buildDepError "prettyprinter"))
            (hsPkgs."process" or (errorHandler.buildDepError "process"))
            (hsPkgs."profunctors" or (errorHandler.buildDepError "profunctors"))
            (hsPkgs."recursion-schemes" or (errorHandler.buildDepError "recursion-schemes"))
            (hsPkgs."reflection" or (errorHandler.buildDepError "reflection"))
            (hsPkgs."semialign" or (errorHandler.buildDepError "semialign"))
            (hsPkgs."sqlite-simple" or (errorHandler.buildDepError "sqlite-simple"))
            (hsPkgs."stm" or (errorHandler.buildDepError "stm"))
            (hsPkgs."streams" or (errorHandler.buildDepError "streams"))
            (hsPkgs."tar" or (errorHandler.buildDepError "tar"))
            (hsPkgs."template-haskell" or (errorHandler.buildDepError "template-haskell"))
            (hsPkgs."temporary" or (errorHandler.buildDepError "temporary"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."these" or (errorHandler.buildDepError "these"))
            (hsPkgs."time" or (errorHandler.buildDepError "time"))
            (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
            (hsPkgs."unordered-containers" or (errorHandler.buildDepError "unordered-containers"))
            (hsPkgs."vector" or (errorHandler.buildDepError "vector"))
            (hsPkgs."witherable" or (errorHandler.buildDepError "witherable"))
            (hsPkgs."zlib" or (errorHandler.buildDepError "zlib"))
            ];
          build-tools = [
            (hsPkgs.buildPackages.tasty-discover or (pkgs.buildPackages.tasty-discover or (errorHandler.buildToolDepError "tasty-discover")))
            ];
          buildable = true;
          modules = [ "Paths_kore" ];
          hsSourceDirs = [ "app/prof" ];
          mainPath = [ "Main.hs" ] ++ (pkgs.lib).optional (!flags.release) "";
          };
        "kore-repl" = {
          depends = [
            (hsPkgs."adjunctions" or (errorHandler.buildDepError "adjunctions"))
            (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
            (hsPkgs."array" or (errorHandler.buildDepError "array"))
            (hsPkgs."async" or (errorHandler.buildDepError "async"))
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."clock" or (errorHandler.buildDepError "clock"))
            (hsPkgs."co-log" or (errorHandler.buildDepError "co-log"))
            (hsPkgs."comonad" or (errorHandler.buildDepError "comonad"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."cryptonite" or (errorHandler.buildDepError "cryptonite"))
            (hsPkgs."data-default" or (errorHandler.buildDepError "data-default"))
            (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."distributive" or (errorHandler.buildDepError "distributive"))
            (hsPkgs."errors" or (errorHandler.buildDepError "errors"))
            (hsPkgs."exceptions" or (errorHandler.buildDepError "exceptions"))
            (hsPkgs."extra" or (errorHandler.buildDepError "extra"))
            (hsPkgs."fgl" or (errorHandler.buildDepError "fgl"))
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            (hsPkgs."free" or (errorHandler.buildDepError "free"))
            (hsPkgs."generic-lens" or (errorHandler.buildDepError "generic-lens"))
            (hsPkgs."generics-sop" or (errorHandler.buildDepError "generics-sop"))
            (hsPkgs."ghc-trace-events" or (errorHandler.buildDepError "ghc-trace-events"))
            (hsPkgs."gitrev" or (errorHandler.buildDepError "gitrev"))
            (hsPkgs."graphviz" or (errorHandler.buildDepError "graphviz"))
            (hsPkgs."groom" or (errorHandler.buildDepError "groom"))
            (hsPkgs."hashable" or (errorHandler.buildDepError "hashable"))
            (hsPkgs."haskeline" or (errorHandler.buildDepError "haskeline"))
            (hsPkgs."integer-gmp" or (errorHandler.buildDepError "integer-gmp"))
            (hsPkgs."kore" or (errorHandler.buildDepError "kore"))
            (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
            (hsPkgs."logict" or (errorHandler.buildDepError "logict"))
            (hsPkgs."megaparsec" or (errorHandler.buildDepError "megaparsec"))
            (hsPkgs."memory" or (errorHandler.buildDepError "memory"))
            (hsPkgs."mmorph" or (errorHandler.buildDepError "mmorph"))
            (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
            (hsPkgs."optparse-applicative" or (errorHandler.buildDepError "optparse-applicative"))
            (hsPkgs."parser-combinators" or (errorHandler.buildDepError "parser-combinators"))
            (hsPkgs."prettyprinter" or (errorHandler.buildDepError "prettyprinter"))
            (hsPkgs."process" or (errorHandler.buildDepError "process"))
            (hsPkgs."profunctors" or (errorHandler.buildDepError "profunctors"))
            (hsPkgs."recursion-schemes" or (errorHandler.buildDepError "recursion-schemes"))
            (hsPkgs."reflection" or (errorHandler.buildDepError "reflection"))
            (hsPkgs."semialign" or (errorHandler.buildDepError "semialign"))
            (hsPkgs."sqlite-simple" or (errorHandler.buildDepError "sqlite-simple"))
            (hsPkgs."stm" or (errorHandler.buildDepError "stm"))
            (hsPkgs."streams" or (errorHandler.buildDepError "streams"))
            (hsPkgs."tar" or (errorHandler.buildDepError "tar"))
            (hsPkgs."template-haskell" or (errorHandler.buildDepError "template-haskell"))
            (hsPkgs."temporary" or (errorHandler.buildDepError "temporary"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."these" or (errorHandler.buildDepError "these"))
            (hsPkgs."time" or (errorHandler.buildDepError "time"))
            (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
            (hsPkgs."unordered-containers" or (errorHandler.buildDepError "unordered-containers"))
            (hsPkgs."vector" or (errorHandler.buildDepError "vector"))
            (hsPkgs."witherable" or (errorHandler.buildDepError "witherable"))
            (hsPkgs."zlib" or (errorHandler.buildDepError "zlib"))
            ];
          build-tools = [
            (hsPkgs.buildPackages.tasty-discover or (pkgs.buildPackages.tasty-discover or (errorHandler.buildToolDepError "tasty-discover")))
            ];
          buildable = true;
          modules = [ "GlobalMain" "Paths_kore" ];
          hsSourceDirs = [ "app/repl" "app/share" ];
          mainPath = ([
            "Main.hs"
            ] ++ (pkgs.lib).optional (!flags.release) "") ++ [ "" ];
          };
        };
      tests = {
        "kore-test" = {
          depends = [
            (hsPkgs."QuickCheck" or (errorHandler.buildDepError "QuickCheck"))
            (hsPkgs."adjunctions" or (errorHandler.buildDepError "adjunctions"))
            (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
            (hsPkgs."array" or (errorHandler.buildDepError "array"))
            (hsPkgs."async" or (errorHandler.buildDepError "async"))
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."call-stack" or (errorHandler.buildDepError "call-stack"))
            (hsPkgs."clock" or (errorHandler.buildDepError "clock"))
            (hsPkgs."co-log" or (errorHandler.buildDepError "co-log"))
            (hsPkgs."comonad" or (errorHandler.buildDepError "comonad"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."cryptonite" or (errorHandler.buildDepError "cryptonite"))
            (hsPkgs."data-default" or (errorHandler.buildDepError "data-default"))
            (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."distributive" or (errorHandler.buildDepError "distributive"))
            (hsPkgs."errors" or (errorHandler.buildDepError "errors"))
            (hsPkgs."exceptions" or (errorHandler.buildDepError "exceptions"))
            (hsPkgs."extra" or (errorHandler.buildDepError "extra"))
            (hsPkgs."fgl" or (errorHandler.buildDepError "fgl"))
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            (hsPkgs."free" or (errorHandler.buildDepError "free"))
            (hsPkgs."generic-lens" or (errorHandler.buildDepError "generic-lens"))
            (hsPkgs."generics-sop" or (errorHandler.buildDepError "generics-sop"))
            (hsPkgs."ghc-trace-events" or (errorHandler.buildDepError "ghc-trace-events"))
            (hsPkgs."gitrev" or (errorHandler.buildDepError "gitrev"))
            (hsPkgs."graphviz" or (errorHandler.buildDepError "graphviz"))
            (hsPkgs."groom" or (errorHandler.buildDepError "groom"))
            (hsPkgs."hashable" or (errorHandler.buildDepError "hashable"))
            (hsPkgs."haskeline" or (errorHandler.buildDepError "haskeline"))
            (hsPkgs."hedgehog" or (errorHandler.buildDepError "hedgehog"))
            (hsPkgs."integer-gmp" or (errorHandler.buildDepError "integer-gmp"))
            (hsPkgs."kore" or (errorHandler.buildDepError "kore"))
            (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
            (hsPkgs."logict" or (errorHandler.buildDepError "logict"))
            (hsPkgs."megaparsec" or (errorHandler.buildDepError "megaparsec"))
            (hsPkgs."memory" or (errorHandler.buildDepError "memory"))
            (hsPkgs."mmorph" or (errorHandler.buildDepError "mmorph"))
            (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
            (hsPkgs."optparse-applicative" or (errorHandler.buildDepError "optparse-applicative"))
            (hsPkgs."parser-combinators" or (errorHandler.buildDepError "parser-combinators"))
            (hsPkgs."prettyprinter" or (errorHandler.buildDepError "prettyprinter"))
            (hsPkgs."process" or (errorHandler.buildDepError "process"))
            (hsPkgs."profunctors" or (errorHandler.buildDepError "profunctors"))
            (hsPkgs."quickcheck-instances" or (errorHandler.buildDepError "quickcheck-instances"))
            (hsPkgs."recursion-schemes" or (errorHandler.buildDepError "recursion-schemes"))
            (hsPkgs."reflection" or (errorHandler.buildDepError "reflection"))
            (hsPkgs."semialign" or (errorHandler.buildDepError "semialign"))
            (hsPkgs."sqlite-simple" or (errorHandler.buildDepError "sqlite-simple"))
            (hsPkgs."stm" or (errorHandler.buildDepError "stm"))
            (hsPkgs."streams" or (errorHandler.buildDepError "streams"))
            (hsPkgs."tar" or (errorHandler.buildDepError "tar"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-golden" or (errorHandler.buildDepError "tasty-golden"))
            (hsPkgs."tasty-hedgehog" or (errorHandler.buildDepError "tasty-hedgehog"))
            (hsPkgs."tasty-hunit" or (errorHandler.buildDepError "tasty-hunit"))
            (hsPkgs."tasty-quickcheck" or (errorHandler.buildDepError "tasty-quickcheck"))
            (hsPkgs."tasty-test-reporter" or (errorHandler.buildDepError "tasty-test-reporter"))
            (hsPkgs."template-haskell" or (errorHandler.buildDepError "template-haskell"))
            (hsPkgs."temporary" or (errorHandler.buildDepError "temporary"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."these" or (errorHandler.buildDepError "these"))
            (hsPkgs."time" or (errorHandler.buildDepError "time"))
            (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
            (hsPkgs."unordered-containers" or (errorHandler.buildDepError "unordered-containers"))
            (hsPkgs."vector" or (errorHandler.buildDepError "vector"))
            (hsPkgs."witherable" or (errorHandler.buildDepError "witherable"))
            (hsPkgs."zlib" or (errorHandler.buildDepError "zlib"))
            ];
          build-tools = [
            (hsPkgs.buildPackages.tasty-discover or (pkgs.buildPackages.tasty-discover or (errorHandler.buildToolDepError "tasty-discover")))
            ];
          buildable = true;
          modules = [
            "Driver"
            "Test/ConsistentKore"
            "Test/Data/Graph/TopologicalSort"
            "Test/Data/Limit"
            "Test/Data/Sup"
            "Test/Debug"
            "Test/Expect"
            "Test/Injection"
            "Test/Kore"
            "Test/Kore/AST/Common"
            "Test/Kore/ASTVerifier/DefinitionVerifier"
            "Test/Kore/ASTVerifier/DefinitionVerifier/Imports"
            "Test/Kore/ASTVerifier/DefinitionVerifier/PatternVerifier"
            "Test/Kore/ASTVerifier/DefinitionVerifier/SentenceVerifier"
            "Test/Kore/ASTVerifier/DefinitionVerifier/SortUsage"
            "Test/Kore/ASTVerifier/DefinitionVerifier/UniqueNames"
            "Test/Kore/ASTVerifier/DefinitionVerifier/UniqueSortVariables"
            "Test/Kore/Attribute/Assoc"
            "Test/Kore/Attribute/Axiom/Concrete"
            "Test/Kore/Attribute/Axiom/Symbolic"
            "Test/Kore/Attribute/Axiom/Unit"
            "Test/Kore/Attribute/Comm"
            "Test/Kore/Attribute/Constructor"
            "Test/Kore/Attribute/Function"
            "Test/Kore/Attribute/Functional"
            "Test/Kore/Attribute/Hook"
            "Test/Kore/Attribute/Idem"
            "Test/Kore/Attribute/Injective"
            "Test/Kore/Attribute/Label"
            "Test/Kore/Attribute/Overload"
            "Test/Kore/Attribute/Owise"
            "Test/Kore/Attribute/Parser"
            "Test/Kore/Attribute/Pattern/ConstructorLike"
            "Test/Kore/Attribute/Pattern/Defined"
            "Test/Kore/Attribute/Pattern/FreeVariables"
            "Test/Kore/Attribute/Pattern/Function"
            "Test/Kore/Attribute/Pattern/Functional"
            "Test/Kore/Attribute/Pattern/Sort"
            "Test/Kore/Attribute/Priority"
            "Test/Kore/Attribute/ProductionID"
            "Test/Kore/Attribute/Simplification"
            "Test/Kore/Attribute/Smtlib"
            "Test/Kore/Attribute/Sort/ConstructorsBuilder"
            "Test/Kore/Attribute/Sort/HasDomainValues"
            "Test/Kore/Attribute/Sort/Unit"
            "Test/Kore/Attribute/SortInjection"
            "Test/Kore/Attribute/Subsort"
            "Test/Kore/Attribute/Symbol"
            "Test/Kore/Attribute/Symbol/Anywhere"
            "Test/Kore/Attribute/Symbol/Klabel"
            "Test/Kore/Attribute/Symbol/Memo"
            "Test/Kore/Attribute/Symbol/NoEvaluators"
            "Test/Kore/Attribute/Symbol/SymbolKywd"
            "Test/Kore/Attribute/Trusted"
            "Test/Kore/Attribute/UniqueId"
            "Test/Kore/BugReport"
            "Test/Kore/Builtin"
            "Test/Kore/Builtin/AssocComm/CeilSimplifier"
            "Test/Kore/Builtin/AssociativeCommutative"
            "Test/Kore/Builtin/Bool"
            "Test/Kore/Builtin/Builtin"
            "Test/Kore/Builtin/Definition"
            "Test/Kore/Builtin/Encoding"
            "Test/Kore/Builtin/Endianness"
            "Test/Kore/Builtin/Inj"
            "Test/Kore/Builtin/Int"
            "Test/Kore/Builtin/InternalBytes"
            "Test/Kore/Builtin/KEqual"
            "Test/Kore/Builtin/Krypto"
            "Test/Kore/Builtin/List"
            "Test/Kore/Builtin/Map"
            "Test/Kore/Builtin/Set"
            "Test/Kore/Builtin/Signedness"
            "Test/Kore/Builtin/String"
            "Test/Kore/Contains"
            "Test/Kore/Equation/Application"
            "Test/Kore/Equation/Sentence"
            "Test/Kore/Error"
            "Test/Kore/Exec"
            "Test/Kore/IndexedModule/Error"
            "Test/Kore/IndexedModule/MockMetadataTools"
            "Test/Kore/IndexedModule/OverloadGraph"
            "Test/Kore/IndexedModule/Resolvers"
            "Test/Kore/IndexedModule/SortGraph"
            "Test/Kore/Internal/ApplicationSorts"
            "Test/Kore/Internal/Condition"
            "Test/Kore/Internal/MultiAnd"
            "Test/Kore/Internal/OrCondition"
            "Test/Kore/Internal/OrPattern"
            "Test/Kore/Internal/Pattern"
            "Test/Kore/Internal/Predicate"
            "Test/Kore/Internal/SideCondition"
            "Test/Kore/Internal/Substitution"
            "Test/Kore/Internal/Symbol"
            "Test/Kore/Internal/TermLike"
            "Test/Kore/Log/DebugEvaluateCondition"
            "Test/Kore/Log/ErrorBottomTotalFunction"
            "Test/Kore/Log/WarnFunctionWithoutEvaluators"
            "Test/Kore/Log/WarnSymbolSMTRepresentation"
            "Test/Kore/Options"
            "Test/Kore/Parser"
            "Test/Kore/Parser/Lexer"
            "Test/Kore/Parser/Parser"
            "Test/Kore/Reachability/Claim"
            "Test/Kore/Reachability/MockAllPath"
            "Test/Kore/Reachability/OnePathStrategy"
            "Test/Kore/Reachability/Prove"
            "Test/Kore/Reachability/SomeClaim"
            "Test/Kore/Repl/Graph"
            "Test/Kore/Repl/Interpreter"
            "Test/Kore/Repl/Parser"
            "Test/Kore/Rewriting/RewritingVariable"
            "Test/Kore/Step"
            "Test/Kore/Step/AntiLeft"
            "Test/Kore/Step/Axiom/EvaluationStrategy"
            "Test/Kore/Step/Axiom/Identifier"
            "Test/Kore/Step/Axiom/Matcher"
            "Test/Kore/Step/Axiom/Registry"
            "Test/Kore/Step/ClaimPattern"
            "Test/Kore/Step/Function/Evaluator"
            "Test/Kore/Step/Function/Integration"
            "Test/Kore/Step/Function/Memo"
            "Test/Kore/Step/Implication"
            "Test/Kore/Step/MockSymbols"
            "Test/Kore/Step/Remainder"
            "Test/Kore/Step/RewriteStep"
            "Test/Kore/Step/Rule"
            "Test/Kore/Step/Rule/Combine"
            "Test/Kore/Step/Rule/Common"
            "Test/Kore/Step/Rule/Expand"
            "Test/Kore/Step/Rule/Simplify"
            "Test/Kore/Step/RulePattern"
            "Test/Kore/Step/Simplification"
            "Test/Kore/Step/Simplification/And"
            "Test/Kore/Step/Simplification/AndTerms"
            "Test/Kore/Step/Simplification/Application"
            "Test/Kore/Step/Simplification/Bottom"
            "Test/Kore/Step/Simplification/Builtin"
            "Test/Kore/Step/Simplification/Ceil"
            "Test/Kore/Step/Simplification/Condition"
            "Test/Kore/Step/Simplification/DomainValue"
            "Test/Kore/Step/Simplification/Equals"
            "Test/Kore/Step/Simplification/Exists"
            "Test/Kore/Step/Simplification/Floor"
            "Test/Kore/Step/Simplification/Forall"
            "Test/Kore/Step/Simplification/Iff"
            "Test/Kore/Step/Simplification/Implies"
            "Test/Kore/Step/Simplification/InjSimplifier"
            "Test/Kore/Step/Simplification/Integration"
            "Test/Kore/Step/Simplification/IntegrationProperty"
            "Test/Kore/Step/Simplification/InternalList"
            "Test/Kore/Step/Simplification/Next"
            "Test/Kore/Step/Simplification/Not"
            "Test/Kore/Step/Simplification/Or"
            "Test/Kore/Step/Simplification/OrPattern"
            "Test/Kore/Step/Simplification/Overloading"
            "Test/Kore/Step/Simplification/Pattern"
            "Test/Kore/Step/Simplification/Rule"
            "Test/Kore/Step/Simplification/StringLiteral"
            "Test/Kore/Step/Simplification/SubstitutionSimplifier"
            "Test/Kore/Step/Simplification/TermLike"
            "Test/Kore/Step/Simplification/Top"
            "Test/Kore/Step/SMT/Builders"
            "Test/Kore/Step/SMT/Evaluator"
            "Test/Kore/Step/SMT/Helpers"
            "Test/Kore/Step/SMT/Representation/All"
            "Test/Kore/Step/SMT/Representation/Builders"
            "Test/Kore/Step/SMT/Representation/Helpers"
            "Test/Kore/Step/SMT/Representation/Sorts"
            "Test/Kore/Step/SMT/Representation/Symbols"
            "Test/Kore/Step/SMT/Sorts"
            "Test/Kore/Step/SMT/Symbols"
            "Test/Kore/Step/SMT/Translate"
            "Test/Kore/Step/Strategy"
            "Test/Kore/Step/Transition"
            "Test/Kore/Syntax/Id"
            "Test/Kore/Syntax/Variable"
            "Test/Kore/TopBottom"
            "Test/Kore/Unification/SubstitutionNormalization"
            "Test/Kore/Unification/Unifier"
            "Test/Kore/Unification/UnifierT"
            "Test/Kore/Unparser"
            "Test/Kore/Variables/Fresh"
            "Test/Kore/Variables/Target"
            "Test/Kore/Variables/V"
            "Test/Kore/Variables/W"
            "Test/Kore/With"
            "Test/Pretty"
            "Test/SMT"
            "Test/SMT/AST"
            "Test/SQL"
            "Test/Stats"
            "Test/Tasty/HUnit/Ext"
            "Test/Terse"
            "Paths_kore"
            ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "Test.hs" ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ./kore;
    }) // { cabal-generator = "hpack"; }