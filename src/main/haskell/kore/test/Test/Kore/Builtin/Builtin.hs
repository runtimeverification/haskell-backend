module Test.Kore.Builtin.Builtin
    ( hookedSymbolDecl
    , pairModule
    , pairModuleName
    , mkPair
    , importKoreModule
    , substitutionSimplifier
    , testSymbol
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import           Kore.AST.Common
import           Kore.AST.Kore
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.Sentence
import qualified Kore.ASTUtils.SmartConstructors as Kore
import           Kore.ASTUtils.SmartPatterns
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..) )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.PredicateSubstitution as PredicateSubstitution
import           Kore.Step.StepperAttributes
import           SMT
                 ( SMT )
import qualified SMT

import Test.Kore

-- | Declare a symbol hooked to the given builtin name.
hookedSymbolDecl
    :: SymbolOrAlias Object
    -- ^ symbol
    -> Sort Object
    -- ^ result sort
    -> [Sort Object]
    -- ^ argument sorts
    -> [CommonKorePattern]
    -- ^ declaration attributes
    -> KoreSentence
hookedSymbolDecl
    SymbolOrAlias { symbolOrAliasConstructor }
    sentenceSymbolResultSort
    sentenceSymbolSorts
    (Attributes -> sentenceSymbolAttributes)
  =
    (asSentence . SentenceHookedSymbol)
        (SentenceSymbol
            { sentenceSymbolSymbol
            , sentenceSymbolSorts
            , sentenceSymbolResultSort
            , sentenceSymbolAttributes
            }
            :: KoreSentenceSymbol Object
        )
  where
    sentenceSymbolSymbol =
        Symbol
            { symbolConstructor = symbolOrAliasConstructor
            , symbolParams = []
            }

pairModuleName :: ModuleName
pairModuleName = ModuleName "PAIR"

{- | Declare the @Pair@ sort and constructors.
 -}
pairModule :: KoreModule
pairModule =
    Module
        { moduleName = pairModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ pairSortDecl
            , pairSymbolDecl
            ]
        }

pairSort :: Sort Object -> Sort Object -> Sort Object
pairSort lSort rSort =
    SortActualSort SortActual
        { sortActualName = testId "Pair"
        , sortActualSorts = [lSort, rSort]
        }

-- | Declare 'Pair' in a Kore module.
pairSortDecl :: KoreSentence
pairSortDecl =
    asSentence decl
  where
    lSortVariable = SortVariable (testId "l")
    rSortVariable = SortVariable (testId "r")
    lSort = SortVariableSort lSortVariable
    rSort = SortVariableSort rSortVariable
    decl :: KoreSentenceSort Object
    decl =
        SentenceSort
            { sentenceSortName =
                let SortActualSort SortActual { sortActualName } =
                        pairSort lSort rSort
                in sortActualName
            , sentenceSortParameters = [lSortVariable, rSortVariable]
            , sentenceSortAttributes = Attributes []
            }

pairId :: Id level
pairId = testId "pair"

symbolPair :: Sort Object -> Sort Object -> SymbolOrAlias Object
symbolPair lSort rSort =
    SymbolOrAlias
        { symbolOrAliasConstructor = pairId
        , symbolOrAliasParams = [lSort, rSort]
        }

pairSymbolDecl :: KoreSentence
pairSymbolDecl =
    asSentence decl
  where
    decl :: KoreSentenceSymbol Object
    decl =
        SentenceSymbol
            { sentenceSymbolSymbol =
                Symbol
                    { symbolConstructor = pairId
                    , symbolParams = [lSortVariable, rSortVariable]
                    }
            , sentenceSymbolSorts = [lSort, rSort]
            , sentenceSymbolResultSort = pairSort lSort rSort
            , sentenceSymbolAttributes =
                Attributes
                    [ constructorAttribute
                    , injectiveAttribute
                    ]
            }
    lSortVariable = SortVariable (testId "l")
    rSortVariable = SortVariable (testId "r")
    lSort = SortVariableSort lSortVariable
    rSort = SortVariableSort rSortVariable

mkPair
    :: Sort Object
    -> Sort Object
    -> CommonPurePattern Object
    -> CommonPurePattern Object
    -> CommonPurePattern Object
mkPair lSort rSort l r = App_ (symbolPair lSort rSort) [l, r]

importKoreModule :: ModuleName -> KoreSentence
importKoreModule moduleName =
    asSentence
        (SentenceImport
            { sentenceImportModuleName = moduleName
            , sentenceImportAttributes = Attributes []
            }
            :: KoreSentenceImport
        )

substitutionSimplifier
    :: MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level Simplifier
substitutionSimplifier tools =
    PredicateSubstitution.create
        tools
        (PureMLPatternSimplifier
            (\_ p ->
                return
                    ( OrOfExpandedPattern.make
                        [ Predicated
                            { term = Kore.mkTop
                            , predicate = Predicate.wrapPredicate p
                            , substitution = []
                            }
                        ]
                    , SimplificationProof
                    )
            )
        )

-- | 'testSymbol' is useful for writing unit tests for symbols.
testSymbol
    :: (CommonPurePattern Object -> SMT (CommonExpandedPattern Object))
    -- ^ evaluator function for the builtin
    -> String
    -- ^ test name
    -> SymbolOrAlias Object
    -- ^ symbol being tested
    -> [CommonPurePattern Object]
    -- ^ arguments for symbol
    -> CommonExpandedPattern Object
    -- ^ expected result
    -> TestTree
testSymbol evaluate title symbol args expected =
    testCase title $ do
        actual <- SMT.runSMT SMT.defaultConfig (evaluate $ App_ symbol args)
        assertEqual "" expected actual
