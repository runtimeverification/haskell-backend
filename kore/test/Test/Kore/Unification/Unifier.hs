module Test.Kore.Unification.Unifier
    ( test_unification
    , test_unsupportedConstructs
    ) where

import Test.Tasty
       ( TestName, TestTree, testGroup )
import Test.Tasty.HUnit
import Test.Tasty.HUnit.Extensions

import           Control.Exception
                 ( ErrorCall (ErrorCall), catch, evaluate )
import           Control.Lens
                 ( Lens', (.~) )
import qualified Control.Lens as Lens
import qualified Data.Bifunctor as Bifunctor
import           Data.Function
import           Data.List.NonEmpty
                 ( NonEmpty ((:|)) )
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Maybe
import qualified Data.Set as Set
import           Data.Text
                 ( Text )

import           Kore.Attribute.Constructor
import           Kore.Attribute.Function
import           Kore.Attribute.Functional
import           Kore.Attribute.Injective
import           Kore.Attribute.SortInjection
import qualified Kore.Attribute.Symbol as Attribute
import           Kore.IndexedModule.MetadataTools hiding
                 ( HeadType (..) )
import qualified Kore.IndexedModule.MetadataTools as HeadType
                 ( HeadType (..) )
import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.Symbol
import           Kore.Internal.TermLike hiding
                 ( V )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import           Kore.Step.Simplification.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Simplification.Data
                 ( Env (..), evalSimplifier )
import qualified Kore.Step.Simplification.Pattern as Pattern
import           Kore.Unification.Error
import           Kore.Unification.Procedure
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unification.UnifierImpl
import qualified Kore.Unification.Unify as Monad.Unify
import           SMT
                 ( SMT )
import qualified SMT

import           Test.Kore
import           Test.Kore.ASTVerifier.DefinitionVerifier
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock

inj :: Sort -> TermLike Variable -> TermLike Variable
inj sortTo pat =
    mkApplySymbol sortTo (injSymbol & parameters .~ [sortFrom, sortTo]) [pat]
  where
    sortFrom = termLikeSort pat

s1, s2, s3, s4 :: Sort
s1 = simpleSort (SortName "s1")
s2 = simpleSort (SortName "s2")
s3 = simpleSort (SortName "s3")
s4 = simpleSort (SortName "s4")

constructor :: Symbol -> Symbol
constructor =
    Lens.set
        (lensSymbolAttributes . Attribute.lensConstructor)
        Attribute.Constructor { isConstructor = True }

functional :: Symbol -> Symbol
functional =
    Lens.set
        (lensSymbolAttributes . Attribute.lensFunctional)
        Attribute.Functional { isDeclaredFunctional = True }

function :: Symbol -> Symbol
function =
    Lens.set
        (lensSymbolAttributes . Attribute.lensFunction)
        Attribute.Function { isDeclaredFunction = True }

injective :: Symbol -> Symbol
injective =
    Lens.set
        (lensSymbolAttributes . Attribute.lensInjective)
        Attribute.Injective { isDeclaredInjective = True }

sortInjection :: Symbol -> Symbol
sortInjection =
    Lens.set
        (lensSymbolAttributes . Attribute.lensSortInjection)
        Attribute.SortInjection { isSortInjection = True }

symbol :: Text -> Symbol
symbol name =
    Symbol
        { symbolConstructor = testId name
        , symbolParams = []
        , symbolAttributes = Attribute.defaultSymbolAttributes
        }

parameters :: Lens' Symbol [Sort]
parameters lens symb@Symbol { symbolParams } =
    (\symbolParams' -> symb { symbolParams = symbolParams' })
    <$> lens symbolParams

var :: Text -> Sort -> Variable
var name variableSort =
    Variable
        { variableName = testId name
        , variableSort
        , variableCounter = mempty
        }

a1Symbol, a2Symbol, a3Symbol, a4Symbol, a5Symbol :: Symbol
a1Symbol = symbol "a1" & constructor & functional & injective
a2Symbol = symbol "a2" & functional
a3Symbol = symbol "a3" & constructor & injective
a4Symbol = symbol "a4" & functional & injective
a5Symbol = symbol "a5" & function

a1, a2, a3, a4, a5 :: TermLike Variable
a1 = mkApplySymbol s1 a1Symbol []
a2 = mkApplySymbol s1 a2Symbol []
a3 = mkApplySymbol s1 a3Symbol []
a4 = mkApplySymbol s1 a4Symbol []
a5 = mkApplySymbol s1 a5Symbol []

aSymbol, bSymbol, fSymbol :: Symbol
aSymbol = symbol "a" & constructor & functional & injective
bSymbol = symbol "b" & constructor & functional & injective
fSymbol = symbol "f" & constructor & functional & injective

a, b :: TermLike Variable
a = mkApplySymbol s1 aSymbol []
b = mkApplySymbol s2 bSymbol []

f :: TermLike Variable -> TermLike Variable
f x' = mkApplySymbol s2 fSymbol [x']

efSymbol, egSymbol, ehSymbol :: Symbol
efSymbol = symbol "ef" & constructor & functional & injective
egSymbol = symbol "eg" & constructor & functional & injective
ehSymbol = symbol "eh" & constructor & functional & injective

ef
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
ef x' y' z' = mkApplySymbol s1 efSymbol [x', y', z']

eg, eh :: TermLike Variable -> TermLike Variable
eg x' = mkApplySymbol s1 egSymbol [x']
eh x' = mkApplySymbol s1 ehSymbol [x']

nonLinFSymbol, nonLinGSymbol, nonLinASymbol, nonLinASSymbol :: Symbol
nonLinFSymbol = symbol "nonLinF" & constructor & functional & injective
nonLinGSymbol = symbol "nonLinG" & constructor & functional & injective
nonLinASymbol = symbol "nonLinA" & constructor & functional & injective
nonLinASSymbol = symbol "nonLinA" & constructor & functional & injective

nonLinF :: TermLike Variable -> TermLike Variable -> TermLike Variable
nonLinF x' y' = mkApplySymbol s1 nonLinFSymbol [x', y']

nonLinG :: TermLike Variable -> TermLike Variable
nonLinG x' = mkApplySymbol s1 nonLinGSymbol [x']

nonLinA, nonLinX, nonLinY :: TermLike Variable
nonLinA = mkApplySymbol s1 nonLinASSymbol []
nonLinX = mkVar $ var "x" s1
nonLinY = mkVar $ var "y" s1

expBinSymbol :: Symbol
expBinSymbol = symbol "times" & constructor & functional & injective

expBin :: TermLike Variable -> TermLike Variable -> TermLike Variable
expBin x' y' = mkApplySymbol s1 expBinSymbol [x', y']

expA, expX, expY :: TermLike Variable
expA = mkVar $ var "a" s1
expX = mkVar $ var "x" s1
expY = mkVar $ var "y" s1

ex1, ex2, ex3, ex4 :: TermLike Variable
ex1 = mkVar $ var "ex1" s1
ex2 = mkVar $ var "ex2" s1
ex3 = mkVar $ var "ex3" s1
ex4 = mkVar $ var "ex4" s1


dv1, dv2 :: TermLike Variable
dv1 =
    mkDomainValue DomainValue
        { domainValueSort = s1
        , domainValueChild = mkStringLiteral "dv1"
        }
dv2 =
    mkDomainValue DomainValue
        { domainValueSort = s1
        , domainValueChild = mkStringLiteral "dv2"
        }

x :: TermLike Variable
x = mkVar $ var "x" s1

xs2 :: TermLike Variable
xs2 = mkVar $ var "xs2" s2

sortParam :: Text -> SortVariable
sortParam name = SortVariable (testId name)

sortParamSort :: Text -> Sort
sortParamSort = SortVariableSort . sortParam

injSymbol :: Symbol
injSymbol =
    symbol "inj"
    & parameters .~ [sortParamSort "From", sortParamSort "To"]
    & functional & injective & sortInjection

symbols :: [Symbol]
symbols =
    [ a1Symbol, a2Symbol, a3Symbol, a4Symbol, a5Symbol
    , aSymbol, bSymbol, fSymbol
    , efSymbol, egSymbol, ehSymbol
    , nonLinFSymbol, nonLinGSymbol, nonLinASymbol, nonLinASSymbol
    , expBinSymbol
    , injSymbol
    ]

symbolAttributesMap :: Map SymbolOrAlias Attribute.Symbol
symbolAttributesMap =
    Map.fromList $ map ((,) <$> toSymbolOrAlias <*> symbolAttributes) symbols

mockStepperAttributes :: SymbolOrAlias -> Attribute.Symbol
mockStepperAttributes patternHead =
    Map.lookup patternHead symbolAttributesMap
    & fromMaybe Attribute.defaultSymbolAttributes

tools :: SmtMetadataTools Attribute.Symbol
tools = MetadataTools
    { symAttributes = mockStepperAttributes
    , symbolOrAliasType = const HeadType.Symbol
    , sortAttributes = undefined
    , isSubsortOf = const $ const False
    , subsorts = Set.singleton
    , applicationSorts = undefined
    , smtData = undefined
    }

testEnv :: Env
testEnv =
    Mock.env
        { metadataTools = tools
        , simplifierPredicate = Mock.substitutionSimplifier
        }

unificationProblem
    :: UnificationTerm
    -> UnificationTerm
    -> TermLike Variable
unificationProblem (UnificationTerm term1) (UnificationTerm term2) =
    mkAnd term1 term2

type Substitution = [(Text, TermLike Variable)]

unificationSubstitution
    :: Substitution
    -> [ (Variable, TermLike Variable) ]
unificationSubstitution = map trans
  where
    trans (v, p) =
        ( Variable
            { variableSort = termLikeSort p
            , variableName = testId v
            , variableCounter = mempty
            }
        , p
        )

unificationResult :: UnificationResult -> Pattern Variable
unificationResult
    UnificationResult { term, substitution, predicate }
  =
    Conditional
        { term
        , predicate
        , substitution =
            Substitution.unsafeWrap $ unificationSubstitution substitution
        }

newtype UnificationTerm = UnificationTerm (TermLike Variable)
data UnificationResult =
    UnificationResult
        { term :: TermLike Variable
        , substitution :: Substitution
        , predicate :: Syntax.Predicate Variable
        }

andSimplifySuccess
    :: HasCallStack
    => UnificationTerm
    -> UnificationTerm
    -> [UnificationResult]
    -> Assertion
andSimplifySuccess term1 term2 results = do
    let expect = map unificationResult results
    Right subst' <-
        runSMT
        $ evalSimplifier testEnv
        $ Monad.Unify.runUnifierT
        $ simplifyAnds (unificationProblem term1 term2 :| [])
    assertEqualWithExplanation "" expect subst'

andSimplifyFailure
    :: HasCallStack
    => UnificationTerm
    -> UnificationTerm
    -> UnificationError
    -> Assertion
andSimplifyFailure term1 term2 err = do
    let expect :: Either UnificationOrSubstitutionError (Pattern Variable)
        expect = Left (UnificationError err)
    actual <-
        runSMT
        $ evalSimplifier testEnv
        $ Monad.Unify.runUnifierT
        $ simplifyAnds (unificationProblem term1 term2 :| [])
    assertEqual "" (show expect) (show actual)

andSimplifyException
    :: HasCallStack
    => String
    -> UnificationTerm
    -> UnificationTerm
    -> String
    -> TestTree
andSimplifyException message term1 term2 exceptionMessage =
    testCase message (catch test handler)
    where
        test = do
            assignment <-
                runSMT $ evalSimplifier testEnv
                $ Monad.Unify.runUnifierT
                $ simplifyAnds (unificationProblem term1 term2 :| [])
            _ <- evaluate assignment
            assertFailure "This evaluation should fail"
        handler (ErrorCall s) = assertEqual "" exceptionMessage s

unificationProcedureSuccessWithSimplifiers
    :: HasCallStack
    => TestName
    -> BuiltinAndAxiomSimplifierMap
    -> UnificationTerm
    -> UnificationTerm
    -> [([(Variable, TermLike Variable)], Syntax.Predicate Variable)]
    -> TestTree
unificationProcedureSuccessWithSimplifiers
    message
    axiomIdToSimplifier
    (UnificationTerm term1)
    (UnificationTerm term2)
    expect
  =
    testCase message $ do
        let mockEnv = testEnv { simplifierAxioms = axiomIdToSimplifier }
        Right results <-
            runSMT
            $ evalSimplifier mockEnv
            $ Monad.Unify.runUnifierT
            $ unificationProcedure term1 term2
        let
            normalize
                :: Predicate Variable
                -> ([(Variable, TermLike Variable)], Syntax.Predicate Variable)
            normalize Conditional { substitution, predicate } =
                (Substitution.unwrap substitution, predicate)
        assertEqualWithExplanation ""
            expect
            (map normalize results)

unificationProcedureSuccess
    :: HasCallStack
    => TestName
    -> UnificationTerm
    -> UnificationTerm
    -> [(Substitution, Syntax.Predicate Variable)]
    -> TestTree
unificationProcedureSuccess message term1 term2 substPredicate =
    unificationProcedureSuccessWithSimplifiers
        message
        Map.empty
        term1
        term2
        expect
  where
    expect =
        map (Bifunctor.first unificationSubstitution) substPredicate

test_unification :: [TestTree]
test_unification =
    [ testCase "Constant" $
        andSimplifySuccess
            (UnificationTerm a)
            (UnificationTerm a)
            [ UnificationResult
                { term = a
                , substitution = []
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "Variable" $
        andSimplifySuccess
            (UnificationTerm x)
            (UnificationTerm a)
            [ UnificationResult
                { term = a
                , substitution = [("x", a)]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "one level" $
        andSimplifySuccess
            (UnificationTerm (f x))
            (UnificationTerm (f a))
            [ UnificationResult
                { term = f a
                , substitution = [("x", a)]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "equal non-constructor patterns" $
        andSimplifySuccess
            (UnificationTerm a2)
            (UnificationTerm a2)
            [ UnificationResult
                { term = a2
                , substitution = []
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "variable + non-constructor pattern" $
        andSimplifySuccess
            (UnificationTerm a2)
            (UnificationTerm x)
            [ UnificationResult
                { term = a2
                , substitution = [("x", a2)]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "https://basics.sjtu.edu.cn/seminars/c_chu/Algorithm.pdf slide 3" $
        andSimplifySuccess
            (UnificationTerm (ef ex1 (eh ex1) ex2))
            (UnificationTerm (ef (eg ex3) ex4 ex3))
            [ UnificationResult
                { term = ef (eg ex3) (eh ex1) ex3
                , substitution =
                    [ ("ex1", eg ex3)
                    , ("ex2", ex3)
                    , ("ex4", eh (eg ex3))
                    ]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "f(g(X),X) = f(Y,a) https://en.wikipedia.org/wiki/Unification_(computer_science)#Examples_of_syntactic_unification_of_first-order_terms" $
        andSimplifySuccess

            (UnificationTerm (nonLinF (nonLinG nonLinX) nonLinX))
            (UnificationTerm (nonLinF nonLinY nonLinA))
            [ UnificationResult
                { term = nonLinF (nonLinG nonLinX) nonLinA
                , substitution =
                    [ ("x", nonLinA)
                    , ("y", nonLinG nonLinA)
                    ]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "times(times(a, y), x) = times(x, times(y, a))" $
        andSimplifySuccess
            (UnificationTerm (expBin (expBin expA expY) expX))
            (UnificationTerm (expBin expX (expBin expY expA)))
            [ UnificationResult
                { term = expBin (expBin expA expY) (expBin expY expA)
                , substitution =
                    [ ("a", expY)
                    , ("x", expBin expY expY)
                    ]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , unificationProcedureSuccess
        "times(x, g(x)) = times(a, a) -- cycle bottom"
        (UnificationTerm (expBin expX (eg expX)))
        (UnificationTerm (expBin expA expA))
        []
    , unificationProcedureSuccess
        "times(times(a, y), x) = times(x, times(y, a))"
        (UnificationTerm (expBin (expBin expA expY) expX))
        (UnificationTerm (expBin expX (expBin expY expA)))
        [   (   [ ("a", expY)
                , ("x", expBin expY expY)
                ]
            , Syntax.Predicate.makeTruePredicate
            )
        ]
    , unificationProcedureSuccess
        "Unifying two non-ctors results in equals predicate"
        (UnificationTerm a2)
        (UnificationTerm a4)
        [ ([], makeEqualsPredicate a2 a4) ]
    , unificationProcedureSuccess
        "Unifying function and variable results in ceil predicate"
        (UnificationTerm x)
        (UnificationTerm a5)
        [   ( [("x", a5)]
            , Syntax.Predicate.makeCeilPredicate a5
            )
        ]
    , testGroup "inj unification tests" injUnificationTests
    , testCase "Unmatching constants is bottom" $
        andSimplifySuccess
            (UnificationTerm a)
            (UnificationTerm a1)
            []
    , testCase "Unmatching domain values is bottom" $
        andSimplifySuccess
            (UnificationTerm dv1)
            (UnificationTerm dv2)
            []
    , andSimplifyException "Unmatching constructor constant + domain value"
        (UnificationTerm a)
        (UnificationTerm dv2)
        "Cannot handle Constructor and DomainValue:\n\
        \a{}()\n\\dv{s1{}}(\"dv2\")\n"
    , andSimplifyException "Unmatching domain value + constructor constant"
        (UnificationTerm dv1)
        (UnificationTerm a)
        "Cannot handle DomainValue and Constructor:\n\
        \\\dv{s1{}}(\"dv1\")\na{}()\n"
    , testCase "Unmatching domain value + nonconstructor constant" $
        andSimplifySuccess
            (UnificationTerm dv1)
            (UnificationTerm a2)
            [ UnificationResult
                { term = dv1
                , substitution = []
                , predicate = makeEqualsPredicate dv1 a2
                }
            ]
    , testCase "Unmatching nonconstructor constant + domain value" $
        andSimplifySuccess
            (UnificationTerm a2)
            (UnificationTerm dv1)
            [ UnificationResult
                { term = a2
                , substitution = []
                , predicate = makeEqualsPredicate a2 dv1
                }
            ]
    , testCase "non-functional pattern" $
        andSimplifyFailure
            (UnificationTerm x)
            (UnificationTerm a3)
            (unsupportedPatterns "Unknown unification case."  x a3)
    , testCase "non-constructor symbolHead right" $
        andSimplifySuccess
            (UnificationTerm a)
            (UnificationTerm a2)
            [ UnificationResult
                { term = a
                , substitution = []
                , predicate = makeEqualsPredicate a a2
                }
            ]
    , testCase "non-constructor symbolHead left" $
        andSimplifySuccess
            (UnificationTerm a2)
            (UnificationTerm a)
            [ UnificationResult
                { term = a2
                , substitution = []
                , predicate = makeEqualsPredicate a2 a
                }
            ]
    , testCase "nested a=a1 is bottom" $
        andSimplifySuccess
            (UnificationTerm (f a))
            (UnificationTerm (f a1))
            []
          {- currently this cannot even be built because of builder checks
    , andSimplifyFailure "Unmatching sorts"
        (UnificationTerm aA)
        (UnificationTerm bA)
        UnificationError
        -}
    , testCase "Maps substitution variables"
        (assertEqualWithExplanation ""
            [(W "1", war' "2")]
            (Substitution.unwrap
                . Substitution.mapVariables showVar
                . Substitution.wrap
                $ [(V 1, var' 2)]
            )
        )

    ]

test_unsupportedConstructs :: TestTree
test_unsupportedConstructs =
    testCase "Unsupported constructs" $
        andSimplifyFailure
            (UnificationTerm (f a))
            (UnificationTerm (f (mkImplies a (mkNext a1))))
            (unsupportedPatterns
                "Unknown unification case."
                a
                (mkImplies a (mkNext a1))
            )

newtype V = V Integer
    deriving (Show, Eq, Ord)

newtype W = W String
    deriving (Show, Eq, Ord)

instance SortedVariable V where
    sortedVariableSort _ = sortVar
    fromVariable = error "Not implemented"
    toVariable = error "Not implemented"

instance SortedVariable W where
    sortedVariableSort _ = sortVar
    fromVariable = error "Not implemented"
    toVariable = error "Not implemented"

instance EqualWithExplanation V where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation W where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

showVar :: V -> W
showVar (V i) = W (show i)

var' :: Integer -> TermLike V
var' i = mkVar (V i)

war' :: String -> TermLike W
war' s = mkVar (W s)

sortVar :: Sort
sortVar = SortVariableSort (SortVariable (Id "#a" AstLocationTest))

injUnificationTests :: [TestTree]
injUnificationTests =
    [ testCase "Injected Variable" $
        andSimplifySuccess
            (UnificationTerm (inj s2 x))
            (UnificationTerm (inj s2 a))
            [ UnificationResult
                { term = inj s2 a
                , substitution = [("x", a)]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "Variable" $
        andSimplifySuccess
            (UnificationTerm xs2)
            (UnificationTerm (inj s2 a))
            [ UnificationResult
                { term = inj s2 a
                , substitution = [("xs2", inj s2 a)]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "Injected Variable vs doubly injected term" $ do
        term2 <-
            simplifyPattern
            $ UnificationTerm (inj s2 (inj s3 a))
        andSimplifySuccess
            (UnificationTerm (inj s2 x))
            term2
            [ UnificationResult
                { term = inj s2 a
                , substitution = [("x", a)]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "doubly injected variable vs injected term" $ do
        term1 <-
            simplifyPattern
            $ UnificationTerm (inj s2 (inj s3 x))
        andSimplifySuccess
            term1
            (UnificationTerm (inj s2 a))
            [ UnificationResult
                { term = inj s2 a
                , substitution = [("x", a)]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "doubly injected variable vs doubly injected term" $ do
        term1 <-
            simplifyPattern
            $ UnificationTerm (inj s2 (inj s4 x))
        term2 <-
            simplifyPattern
            $ UnificationTerm (inj s2 (inj s3 a))
        andSimplifySuccess
            term1
            term2
            [ UnificationResult
                { term = inj s2 a
                , substitution = [("x", a)]
                , predicate = Syntax.Predicate.makeTruePredicate
                }
            ]
    , testCase "constant vs injection is bottom" $
        andSimplifySuccess
            (UnificationTerm a)
            (UnificationTerm (inj s1 xs2))
            []
    , testCase "unmatching nested injections" $ do
        term1 <-
            simplifyPattern
            $ UnificationTerm (inj s4 (inj s2 a))
        term2 <-
            simplifyPattern
            $ UnificationTerm (inj s4 (inj s3 b))
        andSimplifySuccess
            term1
            term2
            []
    , testCase "unmatching injections" $
        andSimplifySuccess
            -- TODO(traiansf): this should succeed if s1 < s2 < s3
            (UnificationTerm (inj s3 a))
            (UnificationTerm (inj s3 xs2))
            []
    ]

simplifyPattern :: UnificationTerm -> IO UnificationTerm
simplifyPattern (UnificationTerm term) = do
    Conditional { term = term' } <- runSMT $ evalSimplifier testEnv simplifier
    return $ UnificationTerm term'
  where
    simplifier = do
        simplifiedPatterns <- Pattern.simplify expandedPattern
        case MultiOr.extractPatterns simplifiedPatterns of
            [] -> return Pattern.bottom
            (config : _) -> return config
    expandedPattern = Pattern.fromTermLike term

makeEqualsPredicate
    :: TermLike Variable
    -> TermLike Variable
    -> Syntax.Predicate Variable
makeEqualsPredicate = Syntax.Predicate.makeEqualsPredicate

runSMT :: SMT a -> IO a
runSMT = SMT.runSMT SMT.defaultConfig emptyLogger
