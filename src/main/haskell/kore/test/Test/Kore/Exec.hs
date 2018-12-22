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
import           Kore.AST.Valid
import           Kore.ASTVerifier.DefinitionVerifier
                 ( AttributesVerification (DoNotVerifyAttributes),
                 verifyAndIndexDefinition )
import           Kore.Attribute.Constructor
import           Kore.Attribute.Functional
import qualified Kore.Builtin as Builtin
import           Kore.Exec
import           Kore.IndexedModule.IndexedModule
                 ( VerifiedModule )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.AxiomPatterns
                 ( AxiomPatternAttributes )
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
            , functionalAxiom "a"
            , functionalAxiom "b"
            , functionalAxiom "c"
            , functionalAxiom "d"
            , rewritesAxiom "a" "b"
            , rewritesAxiom "b" "c"
            , rewritesAxiom "c" "d"
            ]
        , moduleAttributes = Attributes []
        }
    inputPattern = applyToNoArgs mySort "b"
    expected = applyToNoArgs mySort "d"

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
            , functionalAxiom "a"
            , functionalAxiom "b"
            , functionalAxiom "c"
            , functionalAxiom "d"
            , functionalAxiom "e"
            , rewritesAxiom "a" "b"
            , rewritesAxiom "a" "c"
            , rewritesAxiom "c" "d"
            , rewritesAxiom "e" "a"
            ]
        , moduleAttributes = Attributes []
        }
    inputPattern = applyToNoArgs mySort "a"
    expected =
        let
            a = applyToNoArgs mySort "a"
            b = applyToNoArgs mySort "b"
            c = applyToNoArgs mySort "c"
            d = applyToNoArgs mySort "d"
        in
            \case
                ONE -> Set.fromList [b, c]
                STAR -> Set.fromList [a, b, c, d]
                PLUS -> Set.fromList [b, c, d]
                FINAL -> Set.fromList [b, d]

-- | V:MySort{}
searchVar :: CommonStepPattern Object
searchVar =
    mkVar Variable
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
            && resultSort == mySort
            && first == searchVar
          -> Just $ Set.singleton second
        Or_ sort first second
          | sort == mySort
          ->
            liftA2
                Set.union
                (extractSearchResults first)
                (extractSearchResults second)
        _ -> Nothing

verifiedMyModule
    :: VerifiedKoreModule
    -> VerifiedModule StepperAttributes AxiomPatternAttributes
verifiedMyModule module_ = indexedModule
  where
    Just indexedModule = Map.lookup (ModuleName "MY-MODULE") indexedModules
    Right indexedModules = verifyAndIndexDefinition
        DoNotVerifyAttributes
        Builtin.koreVerifiers
        definition
    definition = Definition
        { definitionAttributes = Attributes []
        , definitionModules = [eraseUnifiedSentenceAnnotations <$> module_]
        }

mySortName :: Id Object
mySortName = Id "MySort" AstLocationTest

mySort :: Sort Object
mySort = SortActualSort SortActual
    { sortActualName = mySortName
    , sortActualSorts = []
    }

-- | sort MySort{} []
mySortDecl :: VerifiedKoreSentenceSort Object
mySortDecl = SentenceSort
    { sentenceSortName = mySortName
    , sentenceSortParameters = []
    , sentenceSortAttributes = Attributes []
    }

-- | symbol name{}() : MySort{} [functional{}(), constructor{}()]
constructorDecl :: Text -> VerifiedKoreSentenceSymbol Object
constructorDecl name =
    (mkSymbol_ (testId name) [] mySort)
        { sentenceSymbolAttributes = Attributes
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
functionalAxiom
    :: Text
    -> VerifiedKoreSentence
functionalAxiom name =
    constructUnifiedSentence
        ((<$>) patternPureToKore . SentenceAxiomSentence)
        (mkAxiom
            [UnifiedObject r]
            (mkExists v
                (mkEquals
                    (SortVariableSort r)
                    (mkVar v)
                    (applyToNoArgs mySort name)
                )
            )
        )
            { sentenceAxiomAttributes = Attributes [functionalAttribute] }
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
rewritesAxiom :: Text -> Text -> VerifiedKoreSentence
rewritesAxiom lhsName rhsName =
    constructUnifiedSentence
        ((<$>) patternPureToKore . SentenceAxiomSentence)
        (mkAxiom_
            (mkAnd
                (mkTop mySort)
                (mkAnd
                    (mkTop mySort)
                    (mkRewrites
                        (applyToNoArgs mySort lhsName)
                        (applyToNoArgs mySort rhsName)
                    )
                )
            )
        )

applyToNoArgs :: Sort Object -> Text -> CommonStepPattern Object
applyToNoArgs sort name =
    mkApp
        sort
        SymbolOrAlias
            { symbolOrAliasConstructor = testId name
            , symbolOrAliasParams = []
            }
        []
