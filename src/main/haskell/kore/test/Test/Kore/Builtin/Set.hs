module Test.Kore.Builtin.Set where

import           Hedgehog hiding
                 ( property )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty
import           Test.Tasty.HUnit

import           Control.Error
                 ( runExceptT )
import qualified Control.Monad as Monad
import qualified Control.Monad.Trans as Trans
import qualified Data.Default as Default
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Reflection
                 ( give )
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           Data.Text
                 ( Text )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( fromConcretePurePattern )
import           Kore.AST.Sentence
import qualified Kore.ASTUtils.SmartConstructors as Kore
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTVerifier.DefinitionVerifier
import           Kore.Attribute.Hook
                 ( hookAttribute )
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Builtin as Builtin
import qualified Kore.Builtin.Set as Set
import qualified Kore.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.MetadataTools
import           Kore.Predicate.Predicate as Predicate
import           Kore.Step.AxiomPatterns
                 ( AxiomPattern (..) )
import           Kore.Step.BaseStep
import           Kore.Step.Error
import           Kore.Step.ExpandedPattern
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Pattern as Pattern
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Unification.Data
import           SMT
                 ( SMT )
import qualified SMT

import           Test.Kore
                 ( testId )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import           Test.Kore.Builtin.Builtin
import           Test.Kore.Builtin.Int
                 ( genConcreteIntegerPattern, genInteger, genIntegerPattern )
import qualified Test.Kore.Builtin.Int as Test.Int
import           Test.Kore.Step.Condition.Evaluator
                 ( genSortedVariable )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.SMT

genSetInteger :: Gen (Set Integer)
genSetInteger = Gen.set (Range.linear 0 32) genInteger

genSetConcreteIntegerPattern :: Gen (Set (ConcretePurePattern Object))
genSetConcreteIntegerPattern =
    Set.map Test.Int.asConcretePattern <$> genSetInteger

genSetPattern :: Gen (CommonPurePattern Object)
genSetPattern = asPattern <$> genSetConcreteIntegerPattern

test_getUnit :: TestTree
test_getUnit =
    testPropertyWithSolver
        "in{}(_, unit{}() === \\dv{Bool{}}(\"false\")"
        (do
            patKey <- forAll genIntegerPattern
            let patIn = App_ symbolIn [ patKey, App_ symbolUnit [] ]
                patFalse = Test.Bool.asPattern False
                predicate = mkEquals patFalse patIn
            (===) (Test.Bool.asExpandedPattern False) =<< evaluate patIn
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_inElement :: TestTree
test_inElement =
    testPropertyWithSolver
        "in{}(x, element{}(x)) === \\dv{Bool{}}(\"true\")"
        (do
            patKey <- forAll genIntegerPattern
            let patIn = App_ symbolIn [ patKey, patElement ]
                patElement = App_ symbolElement [ patKey ]
                patTrue = Test.Bool.asPattern True
                predicate = mkEquals patIn patTrue
            (===) (Test.Bool.asExpandedPattern True) =<< evaluate patIn
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_inConcat :: TestTree
test_inConcat =
    testPropertyWithSolver
        "in{}(concat{}(_, element{}(e)), e) === \\dv{Bool{}}(\"true\")"
        (do
            elem' <- forAll genInteger
            values <- forAll genSetConcreteIntegerPattern
            let patIn = App_ symbolIn [ patElem , patSet ]
                patSet =
                    asPattern
                    $ Set.insert (Test.Int.asConcretePattern elem') values
                patElem = Test.Int.asPattern elem'
                patTrue = Test.Bool.asPattern True
                predicate = mkEquals patTrue patIn
            (===) (Test.Bool.asExpandedPattern True) =<< evaluate patIn
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_concatUnit :: TestTree
test_concatUnit =
    testPropertyWithSolver
        "concat{}(unit{}(), xs) === concat{}(xs, unit{}()) === xs"
        (do
            patValues <- forAll genSetPattern
            let patUnit = App_ symbolUnit []
                patConcat1 = App_ symbolConcat [ patUnit, patValues ]
                patConcat2 = App_ symbolConcat [ patValues, patUnit ]
                predicate1 = mkEquals patValues patConcat1
                predicate2 = mkEquals patValues patConcat2
            expect <- evaluate patValues
            (===) expect =<< evaluate patConcat1
            (===) expect =<< evaluate patConcat2
            (===) ExpandedPattern.top =<< evaluate predicate1
            (===) ExpandedPattern.top =<< evaluate predicate2
        )

test_concatAssociates :: TestTree
test_concatAssociates =
    testPropertyWithSolver
        "concat{}(concat{}(as, bs), cs) === concat{}(as, concat{}(bs, cs))"
        (do
            patSet1 <- forAll genSetPattern
            patSet2 <- forAll genSetPattern
            patSet3 <- forAll genSetPattern
            let patConcat12 = App_ symbolConcat [ patSet1, patSet2 ]
                patConcat23 = App_ symbolConcat [ patSet2, patSet3 ]
                patConcat12_3 = App_ symbolConcat [ patConcat12, patSet3 ]
                patConcat1_23 = App_ symbolConcat [ patSet1, patConcat23 ]
                predicate = mkEquals patConcat12_3 patConcat1_23
            concat12_3 <- evaluate patConcat12_3
            concat1_23 <- evaluate patConcat1_23
            (===) concat12_3 concat1_23
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_difference :: TestTree
test_difference =
    testPropertyWithSolver
        "SET.difference is difference"
        (do
            set1 <- forAll genSetConcreteIntegerPattern
            set2 <- forAll genSetConcreteIntegerPattern
            let set3 = Set.difference set1 set2
                patSet3 = asPattern set3
                patDifference =
                    App_ symbolDifference [ asPattern set1, asPattern set2 ]
                predicate = mkEquals patSet3 patDifference
            expect <- evaluate patSet3
            (===) expect =<< evaluate patDifference
            (===) ExpandedPattern.top =<< evaluate predicate
        )

genSetSortedVariable
    :: MetaOrObject level
    => Sort level
    -> Gen (Set (Variable level))
genSetSortedVariable sort =
    Gen.set
        (Range.linear 0 32)
        (genSortedVariable sort)

-- | Sets with symbolic keys are not simplified.
test_symbolic :: TestTree
test_symbolic =
    testPropertyWithSolver
        "builtin functions are not evaluated on symbolic keys"
        (do
            values <- forAll (genSetSortedVariable Test.Int.intSort)
            let patMap = asSymbolicPattern (Set.map mkVar values)
                expect = ExpandedPattern.fromPurePattern patMap
            if Set.null values
                then discard
                else (===) expect =<< evaluate patMap
        )

-- | Construct a pattern for a map which may have symbolic keys.
asSymbolicPattern
    :: Set (CommonPurePattern Object)
    -> CommonPurePattern Object
asSymbolicPattern result
    | Set.null result =
        applyUnit
    | otherwise =
        foldr1 applyConcat (applyElement <$> Set.toAscList result)
  where
    applyUnit = mkDomainValue setSort $ BuiltinDomainSet Set.empty
    applyElement key = App_ symbolElement [key]
    applyConcat set1 set2 = App_ symbolConcat [set1, set2]

{- | Check that unifying a concrete set with itself results in the same set
 -}
test_unifyConcreteIdem :: TestTree
test_unifyConcreteIdem =
    testPropertyWithSolver
        "unify concrete set with itself"
        (give testSymbolOrAliasSorts $ do
            patSet <- forAll genSetPattern
            let patAnd = mkAnd patSet patSet
                predicate = mkEquals patSet patAnd
            expect <- evaluate patSet
            (===) expect =<< evaluate patAnd
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_unifyConcreteDistinct :: TestTree
test_unifyConcreteDistinct =
    testPropertyWithSolver
        "(dis)unify two distinct sets"
        (give testSymbolOrAliasSorts $ do
            set1 <- forAll genSetConcreteIntegerPattern
            patElem <- forAll genConcreteIntegerPattern
            Monad.when (Set.member patElem set1) discard
            let set2 = Set.insert patElem set1
                patSet1 = asPattern set1
                patSet2 = asPattern set2
                conjunction = mkAnd patSet1 patSet2
                predicate = mkEquals patSet1 conjunction
            (===) ExpandedPattern.bottom =<< evaluate conjunction
            (===) ExpandedPattern.bottom =<< evaluate predicate
        )

tree_unifyFramingVariable :: TestTree
tree_unifyFramingVariable =
    testPropertyWithSolver
        "unify a concrete set and a framed set"
        (give testSymbolOrAliasSorts $ do
            framedElem <- forAll genConcreteIntegerPattern
            concreteSet <-
                (<$>)
                    (Set.insert framedElem)
                    (forAll genSetConcreteIntegerPattern)
            frameVar <- forAll (genSortedVariable setSort)
            let patConcreteSet = asPattern concreteSet
                patFramedSet =
                    App_ symbolConcat
                        [ fromConcretePurePattern framedElem
                        , Var_ frameVar
                        ]
                remainder = Set.delete framedElem concreteSet
                patRemainder = asPattern remainder
                expect =
                    Predicated
                        { term = patConcreteSet
                        , predicate = makeTruePredicate
                        , substitution = [(frameVar, patRemainder)]
                        }
            (===) expect =<< evaluate (mkAnd patConcreteSet patFramedSet)
        )

{- | Unify a concrete Set with symbolic-keyed Set.

@
(1, [1]) ∧ (x, [x])
@

Iterated unification must turn the symbolic key @x@ into a concrete key by
unifying the first element of the pair. This also requires that Set unification
return a partial result for unifying the second element of the pair.

 -}
unit_concretizeKeys :: Assertion
unit_concretizeKeys = do
    assertEqual "" expected =<< runSMT (evaluate' original)
  where
    x =
        Variable
            { variableName = testId "x"
            , variableSort = Test.Int.intSort
            }
    key = 1
    symbolicKey = Test.Int.asPattern key
    concreteKey = Test.Int.asConcretePattern key
    concreteSet = asPattern $ Set.fromList [concreteKey]
    symbolic = asSymbolicPattern $ Set.fromList [mkVar x]
    original =
        mkAnd
            (mkPair Test.Int.intSort setSort (Test.Int.asPattern 1) concreteSet)
            (mkPair Test.Int.intSort setSort (mkVar x) symbolic)
    expected =
        Predicated
            { term =
                mkPair Test.Int.intSort setSort
                    symbolicKey
                    (asSymbolicPattern $ Set.fromList [symbolicKey])
            , predicate = Predicate.makeTruePredicate
            , substitution =
                [ (x, symbolicKey) ]
            }

runSMT :: SMT a -> IO a
runSMT = SMT.runSMT SMT.defaultConfig

{- | Unify a concrete Set with symbolic-keyed Set in an axiom

Apply the axiom
@
(x, [x]) => x
@
to the configuration
@
(1, [1])
@
yielding @1@.

Iterated unification must turn the symbolic key @x@ into a concrete key by
unifying the first element of the pair. This also requires that Set unification
return a partial result for unifying the second element of the pair.

 -}
unit_concretizeKeysAxiom :: Assertion
unit_concretizeKeysAxiom = do
    let pair = mkPair Test.Int.intSort setSort symbolicKey concreteSet
    config <- runSMT (evaluate' pair)
    assertEqual "" expected =<< runStep config axiom
  where
    x = mkIntVar (testId "x")
    key = 1
    symbolicKey = Test.Int.asPattern key
    concreteKey = Test.Int.asConcretePattern key
    symbolicSet = asSymbolicPattern $ Set.fromList [x]
    concreteSet = asPattern $ Set.fromList [concreteKey]
    axiom =
        AxiomPattern
            { axiomPatternLeft = mkPair Test.Int.intSort setSort x symbolicSet
            , axiomPatternRight = x
            , axiomPatternRequires = Predicate.makeTruePredicate
            , axiomPatternAttributes = Default.def
            }
    expected =
        Right
            ( Predicated
                { term = symbolicKey
                , predicate =
                    -- The predicate is not discharged because we do not
                    -- provide functionality axioms for elementMap.
                    give testSymbolOrAliasSorts
                    Predicate.makeCeilPredicate
                    $ asSymbolicPattern
                    $ Set.fromList [symbolicKey]
                , substitution = []
                }
            , mconcat
                [ stepProof (StepProofVariableRenamings [])
                , stepProof (StepProofUnification EmptyUnificationProof)
                ]
            )

-- | Specialize 'Set.asPattern' to the builtin sort 'setSort'.
asPattern :: Set.Builtin -> CommonPurePattern Object
Right asPattern = Set.asPattern indexedModule setSort

-- | Specialize 'Set.asPattern' to the builtin sort 'setSort'.
asExpandedPattern :: Set.Builtin -> CommonExpandedPattern Object
Right asExpandedPattern = Set.asExpandedPattern indexedModule setSort

-- | A sort to hook to the builtin @SET.Set@.
setSort :: Sort Object
setSort =
    SortActualSort SortActual
        { sortActualName = testId "Set"
        , sortActualSorts = []
        }

-- | Declare 'setSort' in a Kore module.
setSortDecl :: KoreSentence
setSortDecl =
    (asSentence . SentenceHookedSort) (SentenceSort
        { sentenceSortName =
            let SortActualSort SortActual { sortActualName } = setSort
            in sortActualName
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes [ hookAttribute "SET.Set" ]
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

importBool :: KoreSentence
importBool =
    asSentence
        (SentenceImport
            { sentenceImportModuleName = Test.Bool.boolModuleName
            , sentenceImportAttributes = Attributes []
            }
            :: KoreSentenceImport
        )

setModuleName :: ModuleName
setModuleName = ModuleName "SET"

-- | Make an unparameterized builtin symbol with the given name.
builtinSymbol :: Text -> SymbolOrAlias Object
builtinSymbol name =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId name
        , symbolOrAliasParams = []
        }

symbolUnit :: SymbolOrAlias Object
Right symbolUnit = Set.lookupSymbolUnit setSort indexedModule

symbolElement :: SymbolOrAlias Object
Right symbolElement = Set.lookupSymbolElement setSort indexedModule

symbolConcat :: SymbolOrAlias Object
Right symbolConcat = Set.lookupSymbolConcat setSort indexedModule

symbolIn :: SymbolOrAlias Object
Right symbolIn = Set.lookupSymbolIn setSort indexedModule

symbolDifference :: SymbolOrAlias Object
Right symbolDifference = Set.lookupSymbolDifference setSort indexedModule

{- | Declare the @SET@ builtins.
 -}
setModule :: KoreModule
setModule =
    Module
        { moduleName = setModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ importInt
            , importBool
            , setSortDecl
            , hookedSymbolDecl
                (builtinSymbol "unitSet")
                setSort
                []
                [hookAttribute "SET.unit"]
            , hookedSymbolDecl
                (builtinSymbol "elementSet")
                setSort
                [Test.Int.intSort]
                [hookAttribute "SET.element"]
            , hookedSymbolDecl
                (builtinSymbol "concatSet")
                setSort
                [setSort, setSort]
                [hookAttribute "SET.concat"]
            , hookedSymbolDecl
                (builtinSymbol "inSet")
                Test.Bool.boolSort
                [Test.Int.intSort, setSort]
                [hookAttribute "SET.in"]
            , hookedSymbolDecl
                (builtinSymbol "differenceSet")
                setSort
                [setSort, setSort]
                [hookAttribute "SET.difference"]
            ]
        }

testModuleName :: ModuleName
testModuleName = ModuleName "TEST"

testModule :: KoreModule
testModule =
    Module
        { moduleName = testModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ importKoreModule Test.Bool.boolModuleName
            , importKoreModule Test.Int.intModuleName
            , importKoreModule setModuleName
            , importKoreModule pairModuleName
            ]
        }

evaluate
    :: CommonPurePattern Object
    -> PropertyT SMT (CommonExpandedPattern Object)
evaluate = Trans.lift . evaluate'

evaluate'
    :: CommonPurePattern Object
    -> SMT (CommonExpandedPattern Object)
evaluate' =
    (<$>) fst
    . evalSimplifier
    . Pattern.simplify testTools testSubstitutionSimplifier evaluators

setDefinition :: KoreDefinition
setDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules =
            [ Test.Bool.boolModule
            , Test.Int.intModule
            , pairModule
            , setModule
            , testModule
            ]
        }

indexedModules :: Map ModuleName (KoreIndexedModule StepperAttributes)
indexedModules = verify setDefinition

indexedModule :: KoreIndexedModule StepperAttributes
Just indexedModule = Map.lookup testModuleName indexedModules

evaluators :: Map (Id Object) [Builtin.Function]
evaluators = Builtin.evaluators Set.builtinFunctions indexedModule

verify
    :: ParseAttributes a
    => KoreDefinition
    -> Map ModuleName (KoreIndexedModule a)
verify defn =
    either (error . Kore.Error.printError) id
        (verifyAndIndexDefinition attrVerify Builtin.koreVerifiers defn)
  where
    attrVerify = defaultAttributesVerification Proxy

testSymbolOrAliasSorts :: SymbolOrAliasSorts Object
testTools :: MetadataTools Object StepperAttributes
testTools@MetadataTools { symbolOrAliasSorts = testSymbolOrAliasSorts } =
    extractMetadataTools indexedModule

testSubstitutionSimplifier :: PredicateSubstitutionSimplifier Object Simplifier
testSubstitutionSimplifier = Mock.substitutionSimplifier testTools

runStep
    :: CommonExpandedPattern Object
    -- ^ configuration
    -> AxiomPattern Object
    -- ^ axiom
    -> IO
        (Either
            (StepError Object Variable)
            (CommonExpandedPattern Object, StepProof Object Variable)
        )
runStep configuration axiom =
    (runSMT . evalSimplifier . runExceptT)
        (stepWithAxiom
            testTools
            testSubstitutionSimplifier
            configuration
            axiom
        )

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

mkImplies
    :: CommonPurePattern Object
    -> CommonPurePattern Object
    -> CommonPurePattern Object
mkImplies = give testSymbolOrAliasSorts Kore.mkImplies

mkNot :: CommonPurePattern Object -> CommonPurePattern Object
mkNot = give testSymbolOrAliasSorts Kore.mkNot

mkIntVar :: Id Object -> CommonPurePattern Object
mkIntVar variableName =
    mkVar Variable { variableName, variableSort = Test.Int.intSort }
