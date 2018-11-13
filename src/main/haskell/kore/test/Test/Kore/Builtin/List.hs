module Test.Kore.Builtin.List where

import           Hedgehog hiding
                 ( property )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty

import qualified Control.Monad.Trans as Trans
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Reflection
                 ( give )
import           Data.Sequence
                 ( Seq )
import qualified Data.Sequence as Seq
import           Data.Text
                 ( Text )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.Sentence
import qualified Kore.ASTUtils.SmartConstructors as Kore
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTVerifier.DefinitionVerifier
import           Kore.Attribute.Hook
                 ( hookAttribute )
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Builtin as Builtin
import qualified Kore.Builtin.List as List
import qualified Kore.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.MetadataTools
import           Kore.Step.ExpandedPattern
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Pattern as Pattern
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           SMT
                 ( SMT )

import           Test.Kore
                 ( testId )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import           Test.Kore.Builtin.Builtin
import qualified Test.Kore.Builtin.Int as Test.Int
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.SMT

genInteger :: Gen Integer
genInteger = Gen.integral (Range.linear (-1024) 1024)

genSeqInteger :: Gen (Seq Integer)
genSeqInteger = Gen.seq (Range.linear 0 16) genInteger

test_getUnit :: TestTree
test_getUnit =
    testPropertyWithSolver
        "get{}(unit{}(), _) === \\bottom{}()"
        property
  where
    property = do
        k <- forAll genInteger
        let patGet = App_ symbolGet [App_ symbolUnit [], Test.Int.asPattern k]
            predicate = mkEquals mkBottom patGet
        (===) ExpandedPattern.bottom =<< evaluate patGet
        (===) ExpandedPattern.top =<< evaluate predicate

test_getFirstElement :: TestTree
test_getFirstElement =
    testPropertyWithSolver
        "get{}(concat{}(element{}(e), _), 0) === e"
        property
  where
    property = do
        values <- forAll genSeqInteger
        let patGet = App_ symbolGet [ patList , Test.Int.asPattern 0 ]
            patList = asPattern (Test.Int.asPattern <$> values)
            value =
                case values of
                    Seq.Empty -> Nothing
                    v Seq.:<| _ -> Just v
            patFirst = maybe mkBottom Test.Int.asPattern value
            predicate = mkEquals patGet patFirst
        let expectGet = Test.Int.asPartialExpandedPattern value
        (===) expectGet =<< evaluate patGet
        (===) ExpandedPattern.top =<< evaluate predicate

test_getLastElement :: TestTree
test_getLastElement =
    testPropertyWithSolver
        "get{}(concat{}(_, element{}(e)), -1) === e"
        property
  where
    property = do
        values <- forAll genSeqInteger
        let patGet = App_ symbolGet [ patList , Test.Int.asPattern (-1) ]
            patList = asPattern (Test.Int.asPattern <$> values)
            value =
                case values of
                    Seq.Empty -> Nothing
                    _ Seq.:|> v -> Just v
            patFirst = maybe mkBottom Test.Int.asPattern value
            predicate = give testSymbolOrAliasSorts $ mkEquals patGet patFirst
        let expectGet = Test.Int.asPartialExpandedPattern value
        (===) expectGet =<< evaluate patGet
        (===) ExpandedPattern.top =<< evaluate predicate

test_concatUnit :: TestTree
test_concatUnit =
    testPropertyWithSolver
        "concat{}(unit{}(), xs) === concat{}(xs, unit{}()) === xs"
        property
  where
    property = give testSymbolOrAliasSorts $ do
        values <- forAll genSeqInteger
        let patUnit = App_ symbolUnit []
            patValues = asPattern (Test.Int.asPattern <$> values)
            patConcat1 = App_ symbolConcat [ patUnit, patValues ]
            patConcat2 = App_ symbolConcat [ patValues, patUnit ]
            predicate1 = mkEquals patValues patConcat1
            predicate2 = mkEquals patValues patConcat2
        expectValues <- evaluate patValues
        (===) expectValues =<< evaluate patConcat1
        (===) expectValues =<< evaluate patConcat2
        (===) ExpandedPattern.top =<< evaluate predicate1
        (===) ExpandedPattern.top =<< evaluate predicate2

test_concatAssociates :: TestTree
test_concatAssociates =
    testPropertyWithSolver
        "concat{}(concat{}(as, bs), cs) === concat{}(as, concat{}(bs, cs))"
        property
  where
    property = give testSymbolOrAliasSorts $ do
        values1 <- forAll genSeqInteger
        values2 <- forAll genSeqInteger
        values3 <- forAll genSeqInteger
        let patList1 = asPattern $ Test.Int.asPattern <$> values1
            patList2 = asPattern $ Test.Int.asPattern <$> values2
            patList3 = asPattern $ Test.Int.asPattern <$> values3
            patConcat12 = App_ symbolConcat [ patList1, patList2 ]
            patConcat23 = App_ symbolConcat [ patList2, patList3 ]
            patConcat12_3 = App_ symbolConcat [ patConcat12, patList3 ]
            patConcat1_23 = App_ symbolConcat [ patList1, patConcat23 ]
            predicate = mkEquals patConcat12_3 patConcat1_23
        evalConcat12_3 <- evaluate patConcat12_3
        evalConcat1_23 <- evaluate patConcat1_23
        (===) evalConcat12_3 evalConcat1_23
        (===) ExpandedPattern.top =<< evaluate predicate

-- | Check that simplification is carried out on list elements.
test_simplify :: TestTree
test_simplify =
    testPropertyWithSolver
        "simplify elements"
        property
  where
    property = do
        let
            x =
                mkVar Variable
                    { variableName = testId "x"
                    , variableSort = Test.Int.intSort
                    }
            original =
                mkDomainValue listSort
                $ BuiltinDomainList (Seq.fromList [mkAnd x mkTop])
            expected =
                ExpandedPattern.fromPurePattern
                $ mkDomainValue listSort
                $ BuiltinDomainList (Seq.fromList [x])
        (===) expected =<< evaluate original

-- | Specialize 'List.asPattern' to the builtin sort 'listSort'.
asPattern :: List.Builtin Variable -> CommonPurePattern Object
Right asPattern = List.asPattern indexedModule listSort

-- | Specialize 'List.asPattern' to the builtin sort 'listSort'.
asExpandedPattern :: List.Builtin Variable -> CommonExpandedPattern Object
Right asExpandedPattern = List.asExpandedPattern indexedModule listSort

-- | A sort to hook to the builtin @LIST.List@.
listSort :: Sort Object
listSort =
    SortActualSort SortActual
        { sortActualName = testId "List"
        , sortActualSorts = []
        }

-- | Another sort with the same hook
listSort2 :: Sort Object
listSort2 =
    SortActualSort SortActual
        { sortActualName = testId "List2"
        , sortActualSorts = []
        }

-- | Declare 'listSort' in a Kore module.
listSortDecl :: KoreSentence
listSortDecl =
    (asSentence . SentenceHookedSort) (SentenceSort
        { sentenceSortName =
            let SortActualSort SortActual { sortActualName } = listSort
            in sortActualName
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes [ hookAttribute "LIST.List" ]
        }
        :: KoreSentenceSort Object)

-- | Declare 'listSort' in a Kore module.
listSortDecl2 :: KoreSentence
listSortDecl2 =
    (asSentence . SentenceHookedSort) (SentenceSort
        { sentenceSortName =
            let SortActualSort SortActual { sortActualName } = listSort2
            in sortActualName
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes [ hookAttribute "LIST.List" ]
        }
        :: KoreSentenceSort Object)

importInt :: KoreSentence
importInt =
    asSentence
        (SentenceImport
            { sentenceImportModuleName = Test.Int.intModuleName
            , sentenceImportAttributes = Attributes []
            }
            :: KoreSentenceImport
        )

listModuleName :: ModuleName
listModuleName = ModuleName "LIST"

-- | Make an unparameterized builtin symbol with the given name.
builtinSymbol :: Text -> SymbolOrAlias Object
builtinSymbol name =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId name
        , symbolOrAliasParams = []
        }

symbolUnit :: SymbolOrAlias Object
Right symbolUnit = List.lookupSymbolUnit listSort indexedModule

symbolElement :: SymbolOrAlias Object
Right symbolElement = List.lookupSymbolElement listSort indexedModule

symbolConcat :: SymbolOrAlias Object
Right symbolConcat = List.lookupSymbolConcat listSort indexedModule

symbolGet :: SymbolOrAlias Object
Right symbolGet = List.lookupSymbolGet listSort indexedModule

{- | Declare the @LIST@ builtins.
 -}
listModule :: KoreModule
listModule =
    Module
        { moduleName = listModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ importInt
            , listSortDecl
            , hookedSymbolDecl
                (builtinSymbol "unitList")
                listSort
                []
                [hookAttribute "LIST.unit"]
            , hookedSymbolDecl
                (builtinSymbol "elementList")
                listSort
                [Test.Int.intSort]
                [hookAttribute "LIST.element"]
            , hookedSymbolDecl
                (builtinSymbol "concatList")
                listSort
                [listSort, listSort]
                [hookAttribute "LIST.concat"]
            , hookedSymbolDecl
                (builtinSymbol "getList")
                Test.Int.intSort
                [listSort, Test.Int.intSort]
                [hookAttribute "LIST.get"]
            -- A second collection of hooked sorts and symbols
            -- To test that `asPattern` picks the right one
            , listSortDecl2
            , hookedSymbolDecl
                (builtinSymbol "unitList2")
                listSort2
                []
                [hookAttribute "LIST.unit"]
            , hookedSymbolDecl
                (builtinSymbol "elementList2")
                listSort2
                [Test.Int.intSort]
                [hookAttribute "LIST.element"]
            , hookedSymbolDecl
                (builtinSymbol "concatList2")
                listSort2
                [listSort2, listSort2]
                [hookAttribute "LIST.concat"]
            , hookedSymbolDecl
                (builtinSymbol "getList2")
                Test.Int.intSort
                [listSort2, Test.Int.intSort]
                [hookAttribute "LIST.get"]
            ]
        }

evaluate
    :: CommonPurePattern Object
    -> PropertyT SMT (CommonExpandedPattern Object)
evaluate pat =
    (<$>) fst
    $ Trans.lift
    $ evalSimplifier
    $ Pattern.simplify
        testTools
        testSubstitutionSimplifier
        evaluators
        pat

mapDefinition :: KoreDefinition
mapDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules =
            [ Test.Bool.boolModule
            , Test.Int.intModule
            , listModule
            ]
        }

indexedModules :: Map ModuleName (KoreIndexedModule StepperAttributes)
indexedModules = verify mapDefinition

indexedModule :: KoreIndexedModule StepperAttributes
Just indexedModule = Map.lookup listModuleName indexedModules

evaluators :: Map (Id Object) [Builtin.Function]
evaluators = Builtin.evaluators List.builtinFunctions indexedModule

verify
    :: ParseAttributes a
    => KoreDefinition
    -> Map ModuleName (KoreIndexedModule a)
verify defn =
    either (error . Kore.Error.printError) id
        (verifyAndIndexDefinition attrVerify Builtin.koreVerifiers defn)
  where
    attrVerify = defaultAttributesVerification Proxy

testTools :: MetadataTools Object StepperAttributes
testSymbolOrAliasSorts :: SymbolOrAliasSorts Object
testTools@MetadataTools { symbolOrAliasSorts = testSymbolOrAliasSorts } =
    extractMetadataTools indexedModule

testSubstitutionSimplifier :: PredicateSubstitutionSimplifier Object Simplifier
testSubstitutionSimplifier = Mock.substitutionSimplifier testTools

-- * Constructors

mkBottom :: CommonPurePattern Object
mkBottom = Kore.mkBottom

mkEquals
    :: CommonPurePattern Object
    -> CommonPurePattern Object
    -> CommonPurePattern Object
mkEquals = give testSymbolOrAliasSorts Kore.mkEquals

mkAnd
    :: CommonPurePattern Object
    -> CommonPurePattern Object
    -> CommonPurePattern Object
mkAnd = give testSymbolOrAliasSorts Kore.mkAnd

mkTop :: CommonPurePattern Object
mkTop = Kore.mkTop

mkVar :: Variable Object -> CommonPurePattern Object
mkVar = give testSymbolOrAliasSorts Kore.mkVar

mkDomainValue
    :: Sort Object
    -> BuiltinDomain (CommonPurePattern Object)
    -> CommonPurePattern Object
mkDomainValue = give testSymbolOrAliasSorts Kore.mkDomainValue
