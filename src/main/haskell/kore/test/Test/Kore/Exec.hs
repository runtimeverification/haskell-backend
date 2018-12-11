module Test.Kore.Exec
    ( test_exec
    , test_search
    ) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( testCase )

import           Control.Applicative
                 ( liftA2 )
import           Data.Limit
                 ( Limit (Unlimited) )
import qualified Data.Map as Map
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           Data.Text
                 ( Text )

import           Kore.AST.Kore
import           Kore.AST.PureToKore
import           Kore.AST.Sentence
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTVerifier.DefinitionVerifier
                 ( AttributesVerification (DoNotVerifyAttributes),
                 verifyAndIndexDefinition )
import           Kore.Attribute.Constructor
import           Kore.Attribute.Functional
import qualified Kore.Builtin as Builtin
import           Kore.Exec
import           Kore.Implicit.ImplicitSorts
                 ( predicateSort )
import           Kore.IndexedModule.IndexedModule
                 ( VerifiedModule )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..) )
import           Kore.Step.Pattern
import           Kore.Step.Search
                 ( SearchType (..) )
import qualified Kore.Step.Search as Search
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import           Kore.Step.Step
                 ( allRewrites, anyRewrite )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )
import qualified SMT

import Test.Kore
import Test.Kore.Comparators ()
import Test.Tasty.HUnit.Extensions

test_exec :: TestTree
test_exec = testCase "exec" $ actual >>= assertEqualWithExplanation "" expected
  where
    actual = SMT.runSMT SMT.defaultConfig $ evalSimplifier $ exec
        verifiedModule
        inputPattern
        Unlimited
        anyRewrite
    verifiedModule = verifiedMyModule Module
        { moduleName = ModuleName "MY-MODULE"
        , moduleSentences =
            [ asSentence $ mySortDecl
            , asSentence $ constructorDecl "a"
            , asSentence $ constructorDecl "b"
            , asSentence $ constructorDecl "c"
            , asSentence $ constructorDecl "d"
            , asKoreAxiomSentence $ functionalAxiom "a"
            , asKoreAxiomSentence $ functionalAxiom "b"
            , asKoreAxiomSentence $ functionalAxiom "c"
            , asKoreAxiomSentence $ functionalAxiom "d"
            , asKoreAxiomSentence $ rewritesAxiom "a" "b"
            , asKoreAxiomSentence $ rewritesAxiom "b" "c"
            , asKoreAxiomSentence $ rewritesAxiom "c" "d"
            ]
        , moduleAttributes = Attributes []
        }
    inputPattern = applyToNoArgs "b"
    expected = applyToNoArgs "d"

test_search :: TestTree
test_search =
    testGroup
        "search"
        [ makeTestCase searchType | searchType <- [ ONE, STAR, PLUS, FINAL] ]
  where
    makeTestCase searchType =
        testCase (show searchType) (assertion searchType)
    assertion searchType = actual searchType
        >>= assertEqualWithExplanation "" (expected searchType)
    actual searchType = do
        let
            simplifier = search
                verifiedModule
                inputPattern
                Unlimited
                allRewrites
                searchPattern
                Search.Config { bound = Unlimited, searchType }
        finalPattern <- SMT.runSMT SMT.defaultConfig $ evalSimplifier simplifier
        let Just results = extractSearchResults finalPattern
        return results
    verifiedModule = verifiedMyModule Module
        { moduleName = ModuleName "MY-MODULE"
        , moduleSentences =
            [ asSentence $ mySortDecl
            , asSentence $ constructorDecl "a"
            , asSentence $ constructorDecl "b"
            , asSentence $ constructorDecl "c"
            , asSentence $ constructorDecl "d"
            , asSentence $ constructorDecl "e"
            , asKoreAxiomSentence $ functionalAxiom "a"
            , asKoreAxiomSentence $ functionalAxiom "b"
            , asKoreAxiomSentence $ functionalAxiom "c"
            , asKoreAxiomSentence $ functionalAxiom "d"
            , asKoreAxiomSentence $ functionalAxiom "e"
            , asKoreAxiomSentence $ rewritesAxiom "a" "b"
            , asKoreAxiomSentence $ rewritesAxiom "a" "c"
            , asKoreAxiomSentence $ rewritesAxiom "c" "d"
            , asKoreAxiomSentence $ rewritesAxiom "e" "a"
            ]
        , moduleAttributes = Attributes []
        }
    inputPattern = applyToNoArgs "a"
    expected =
        let
            a = applyToNoArgs "a"
            b = applyToNoArgs "b"
            c = applyToNoArgs "c"
            d = applyToNoArgs "d"
        in
            \case
                ONE -> Set.fromList [b, c]
                STAR -> Set.fromList [a, b, c, d]
                PLUS -> Set.fromList [b, c, d]
                FINAL -> Set.fromList [b, d]

-- | V:MySort{}
searchVar :: CommonStepPattern Object
searchVar =
    Var_ Variable
        { variableName = Id "V" AstLocationTest
        , variableSort = mySort
        }

-- |
--  \and{MySort{}}(
--      V:MySort{},
--      \top{MySort{}}())
searchPattern :: CommonExpandedPattern Object
searchPattern = Predicated
    { term = searchVar
    , predicate = makeTruePredicate
    , substitution = mempty
    }

-- | Turn a disjunction of "v = ???" into Just a set of the ???. If the input is
-- not a disjunction of "v = ???", return Nothing.
extractSearchResults
    :: CommonStepPattern Object -> Maybe (Set (CommonStepPattern Object))
extractSearchResults =
    \case
        Equals_ operandSort resultSort first second
          | operandSort == mySort
            && resultSort == predicateSort
            && first == searchVar
          -> Just $ Set.singleton second
        Or_ sort first second
          | sort == predicateSort
          ->
            liftA2
                Set.union
                (extractSearchResults first)
                (extractSearchResults second)
        _ -> Nothing

verifiedMyModule :: KoreModule -> VerifiedModule StepperAttributes
verifiedMyModule module_ = indexedModule
  where
    Just indexedModule = Map.lookup (ModuleName "MY-MODULE") indexedModules
    Right indexedModules = verifyAndIndexDefinition
        DoNotVerifyAttributes
        Builtin.koreVerifiers
        definition
    definition = Definition
        { definitionAttributes = Attributes []
        , definitionModules = [module_]
        }

mySortName :: Id Object
mySortName = Id "MySort" AstLocationTest

mySort :: Sort Object
mySort = SortActualSort SortActual
    { sortActualName = mySortName
    , sortActualSorts = []
    }

-- | sort MySort{} []
mySortDecl :: KoreSentenceSort Object
mySortDecl = SentenceSort
    { sentenceSortName = mySortName
    , sentenceSortParameters = []
    , sentenceSortAttributes = Attributes []
    }

-- | symbol name{}() : MySort{} [functional{}(), constructor{}()]
constructorDecl :: Text -> KoreSentenceSymbol Object
constructorDecl name = SentenceSymbol
    { sentenceSymbolSymbol =
        Symbol
            { symbolConstructor = Id name AstLocationTest
            , symbolParams = []
            }
    , sentenceSymbolSorts = []
    , sentenceSymbolResultSort = mySort
    , sentenceSymbolAttributes = Attributes
        [ functionalAttribute
        , constructorAttribute
        ]
    }

-- |
--  axiom{R}
--      \exists{R}(
--          V:MySort{},
--          \equals{MySort{}, R}(
--              V:MySort{},
--              a{}()))
--  [functional{}()]
functionalAxiom :: Text -> KoreSentenceAxiom
functionalAxiom name = SentenceAxiom
    { sentenceAxiomParameters = [UnifiedObject r]
    , sentenceAxiomPattern =
        asCommonKorePattern $ ExistsPattern Exists
            { existsSort = SortVariableSort r
            , existsVariable = v
            , existsChild =
                asCommonKorePattern $ EqualsPattern Equals
                    { equalsOperandSort = mySort
                    , equalsResultSort = SortVariableSort r
                    , equalsFirst = asCommonKorePattern $ VariablePattern v
                    , equalsSecond = patternPureToKore $ applyToNoArgs name
                    }
            }
    , sentenceAxiomAttributes = Attributes [functionalAttribute]
    }
  where
    v = Variable
        { variableName = Id "V" AstLocationTest
        , variableSort = mySort
        }
    r = SortVariable $ Id "R" AstLocationTest

-- |
--  axiom{}
--      \and{MySort{}}(
--          \top{MySort{}}(),
--          \and{MySort{}}(),
--              \top{MySort{}}(),
--              \rewrites{MySort{}}(
--                  lhsName{}(),
--                  rhsName{}())))
--  []
rewritesAxiom :: Text -> Text -> KoreSentenceAxiom
rewritesAxiom lhsName rhsName = SentenceAxiom
    { sentenceAxiomParameters = []
    , sentenceAxiomPattern = asCommonKorePattern $ AndPattern And
        { andSort = mySort
        , andFirst = asCommonKorePattern $ TopPattern $ Top mySort
        , andSecond = asCommonKorePattern $ AndPattern And
            { andSort = mySort
            , andFirst = asCommonKorePattern $ TopPattern $ Top mySort
            , andSecond = asCommonKorePattern $ RewritesPattern Rewrites
                { rewritesSort = mySort
                , rewritesFirst = patternPureToKore $ applyToNoArgs lhsName
                , rewritesSecond = patternPureToKore $ applyToNoArgs rhsName
                }
            }
        }
    , sentenceAxiomAttributes = Attributes []
    }

applyToNoArgs :: Text -> CommonStepPattern Object
applyToNoArgs name =
    App_
    (SymbolOrAlias
        { symbolOrAliasConstructor = testId name
        , symbolOrAliasParams = []
        }
    )
    []
