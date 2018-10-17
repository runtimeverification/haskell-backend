module Test.Kore.Unification.Unifier (test_unification) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( assertEqual, assertFailure, testCase )
import Test.Tasty.HUnit.Extensions

import           Control.Exception
                 ( ErrorCall (ErrorCall), catch, evaluate )
import           Control.Monad.Counter
                 ( evalCounter )
import           Control.Monad.Except
                 ( runExceptT )
import           Data.CallStack
import           Data.Default
                 ( def )
import           Data.Function
                 ( on )
import           Data.Functor.Foldable
import           Data.List
                 ( sortBy )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Reflection
                 ( give )
import           Data.Text
                 ( Text )

import           Kore.AST.Builders
import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.MLPatterns
import           Kore.AST.PureML
import           Kore.AST.Sentence
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.ASTPrettyPrint
import           Kore.ASTUtils.SmartConstructors
                 ( mkSort, mkVar )
import           Kore.IndexedModule.MetadataTools
import           Kore.Predicate.Predicate
                 ( Predicate, makeCeilPredicate, makeFalsePredicate,
                 makeTruePredicate )
import qualified Kore.Predicate.Predicate as Predicate
                 ( makeEqualsPredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( Predicated (..), bottom )
import qualified Kore.Step.ExpandedPattern as PredicateSubstitution
                 ( PredicateSubstitution (..) )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.Simplification.Simplifier as Simplifier
import           Kore.Step.StepperAttributes
import           Kore.Unification.Data
import           Kore.Unification.Error
import           Kore.Unification.Procedure
import           Kore.Unification.UnifierImpl

import           Test.Kore
import           Test.Kore.AST.MLPatterns
                 ( extractPurePattern )
import           Test.Kore.ASTVerifier.DefinitionVerifier
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSimplifiers as Mock

bottomPredicate :: CommonPurePatternStub Object
bottomPredicate = withSort (mkSort "PREDICATE") bottom_

applyInj
    :: Sort Object
    -> Sort Object
    -> CommonPurePatternStub Object -> CommonPurePatternStub Object
applyInj sortFrom sortTo pat = applyPS symbolInj [sortFrom, sortTo] [pat]

s1, s2, s3, s4 :: Sort Object
s1 = simpleSort (SortName "s1")
s2 = simpleSort (SortName "s2")
s3 = simpleSort (SortName "s3")
s4 = simpleSort (SortName "s4")

a, a1, a2, a3, a4, a5, b, c, f, g, h :: PureSentenceSymbol Object
a = symbol_ "a" AstLocationTest [] s1
a1 = symbol_ "a1" AstLocationTest [] s1
a2 = symbol_ "a2" AstLocationTest [] s1
a3 = symbol_ "a3" AstLocationTest [] s1
a4 = symbol_ "a4" AstLocationTest [] s1
a5 = symbol_ "a5" AstLocationTest [] s1
b = symbol_ "b" AstLocationTest [] s2
c = symbol_ "c" AstLocationTest [] s3
f = symbol_ "f" AstLocationTest [s1] s2
g = symbol_ "g" AstLocationTest [s1, s2] s3
h = symbol_ "h" AstLocationTest [s1, s2, s3] s1

ef, eg, eh :: PureSentenceSymbol Object
ef = symbol_ "ef" AstLocationTest [s1, s1, s1] s1
eg = symbol_ "eg" AstLocationTest [s1] s1
eh = symbol_ "eh" AstLocationTest [s1] s1

nonLinF, nonLinG, nonLinAS :: PureSentenceSymbol Object
nonLinF = symbol_ "nonLinF" AstLocationTest [s1, s1] s1
nonLinG = symbol_ "nonLinG" AstLocationTest [s1] s1
nonLinAS = symbol_ "nonLinA" AstLocationTest [] s1

nonLinA, nonLinX, nonLinY :: CommonPurePatternStub Object
nonLinX = parameterizedVariable_ s1 "x" AstLocationTest
nonLinY = parameterizedVariable_ s1 "y" AstLocationTest

nonLinA = applyS nonLinAS []

expBin :: PureSentenceSymbol Object
expBin = symbol_ "times" AstLocationTest [s1, s1] s1

expA, expX, expY :: CommonPurePatternStub Object
expA = parameterizedVariable_ s1 "a" AstLocationTest
expX = parameterizedVariable_ s1 "x" AstLocationTest
expY = parameterizedVariable_ s1 "y" AstLocationTest

ex1, ex2, ex3, ex4 :: CommonPurePatternStub Object
ex1 = parameterizedVariable_ s1 "ex1" AstLocationTest
ex2 = parameterizedVariable_ s1 "ex2" AstLocationTest
ex3 = parameterizedVariable_ s1 "ex3" AstLocationTest
ex4 = parameterizedVariable_ s1 "ex4" AstLocationTest


dv1, dv2 :: CommonPurePatternStub Object
dv1 = parameterizedDomainValue_ s1 "dv1"
dv2 = parameterizedDomainValue_ s1 "dv2"

aA :: CommonPurePatternStub Object
aA = applyS a []

a1A :: CommonPurePatternStub Object
a1A = applyS a1 []

a2A :: CommonPurePatternStub Object
a2A = applyS a2 []

a3A :: CommonPurePatternStub Object
a3A = applyS a3 []

a4A :: CommonPurePatternStub Object
a4A = applyS a4 []

a5A :: CommonPurePatternStub Object
a5A = applyS a5 []

bA :: CommonPurePatternStub Object
bA = applyS b []

x :: CommonPurePatternStub Object
x = parameterizedVariable_ s1 "x" AstLocationTest

xs2 :: CommonPurePatternStub Object
xs2 = parameterizedVariable_ s2 "xs2" AstLocationTest

symbols :: [(SymbolOrAlias Object, PureSentenceSymbol Object)]
symbols =
    map
        (\s -> (getSentenceSymbolOrAliasHead s [], s))
        [ a, a1, a2, a3, a4, a5, b, c, f, g, h
        , ef, eg, eh
        , nonLinF, nonLinG, nonLinAS
        , expBin
        ]

sortParam :: Text -> SortVariable level
sortParam name = sortParameter Proxy name AstLocationTest

sortParamSort :: Text -> Sort level
sortParamSort = SortVariableSort . sortParam

injName :: Text
injName = "inj"

symbolInj :: PureSentenceSymbol level
symbolInj =
    parameterizedSymbol_ injName AstLocationImplicit
        [sortParam "From", sortParam "To"]
        [sortParamSort "From"]
        (sortParamSort "To")

isInjHead :: SymbolOrAlias level -> Bool
isInjHead pHead = getId (symbolOrAliasConstructor pHead) == injName

mockStepperAttributes :: SymbolOrAlias Object -> StepperAttributes
mockStepperAttributes patternHead = StepperAttributes
    { isConstructor =
           patternHead /= getSentenceSymbolOrAliasHead a2 []
        && patternHead /= getSentenceSymbolOrAliasHead a4 []
        && patternHead /= getSentenceSymbolOrAliasHead a5 []
        && not (isInjHead patternHead)
    , isFunctional =
           patternHead /= getSentenceSymbolOrAliasHead a3 []
        && patternHead /= getSentenceSymbolOrAliasHead a5 []
    , isFunction = patternHead == getSentenceSymbolOrAliasHead a5 []
    , isInjective =
        (  patternHead /= getSentenceSymbolOrAliasHead a2 []
        && patternHead /= getSentenceSymbolOrAliasHead a5 []
        )
        || isInjHead patternHead
    , isSortInjection = isInjHead patternHead
    , hook = def
    }

mockGetArgumentSorts :: SymbolOrAlias Object -> [Sort Object]
mockGetArgumentSorts patternHead
    | isInjHead patternHead = init (symbolOrAliasParams patternHead)
    | otherwise =
        maybe
            (error ("Unexpected Head " ++  show patternHead))
            getSentenceSymbolOrAliasArgumentSorts
            (lookup patternHead symbols)

mockGetResultSort :: SymbolOrAlias Object -> Sort Object
mockGetResultSort patternHead
    | isInjHead patternHead = last (symbolOrAliasParams patternHead)
    | otherwise =
        maybe
            (error ("Unexpected Head " ++  show patternHead))
            getSentenceSymbolOrAliasResultSort
            (lookup patternHead symbols)

mockSymbolOrAliasSorts :: SymbolOrAliasSorts Object
mockSymbolOrAliasSorts pHead = ApplicationSorts
    { applicationSortsOperands = mockGetArgumentSorts pHead
    , applicationSortsResult = mockGetResultSort pHead
    }

tools :: MetadataTools Object StepperAttributes
tools = MetadataTools
    { symAttributes = mockStepperAttributes
    , sortAttributes = undefined
    , symbolOrAliasSorts = mockSymbolOrAliasSorts
    , isSubsortOf = const $ const False
    }

unificationProblem
    :: MetaOrObject level
    => UnificationTerm level
    -> UnificationTerm level
    -> CommonPurePattern level
unificationProblem (UnificationTerm term1) (UnificationTerm term2) =
    extractPurePattern (and_ term1 term2)

type Substitution level =  [(Text, CommonPurePatternStub level)]

unificationSubstitution
    :: Substitution Object
    -> [ (Variable Object, CommonPurePattern Object) ]
unificationSubstitution = map trans
  where
    trans (v, p) =
        let pp = extractPurePattern p in
            ( Variable
                { variableSort =
                    getPatternResultSort mockSymbolOrAliasSorts (project pp)
                , variableName = testId v
                }
            , pp
            )

unificationResult
    :: UnificationResultTerm Object
    -> Substitution Object
    -> Predicate Object Variable
    -> ExpandedPattern Object Variable
unificationResult (UnificationResultTerm pat) sub predicate =
    Predicated
        { term = extractPurePattern pat
        , predicate = predicate
        , substitution = unificationSubstitution sub
        }

newtype UnificationTerm level =
    UnificationTerm (CommonPurePatternStub level)
newtype UnificationResultTerm level =
    UnificationResultTerm (CommonPurePatternStub level)

andSimplifySuccess
    :: (HasCallStack)
    => String
    -> UnificationTerm Object
    -> UnificationTerm Object
    -> UnificationResultTerm Object
    -> Substitution Object
    -> Predicate Object Variable
    -> UnificationProof Object Variable
    -> TestTree
andSimplifySuccess message term1 term2 resultTerm subst predicate proof =
    testCase
        message
        (assertEqualWithExplanation
            ""
            (unificationResult resultTerm subst predicate, proof)
            (subst'', proof')
        )
  where
    Right (subst', proof') =
        evalCounter
        . runExceptT
        $ simplifyAnds tools [(unificationProblem term1 term2)]

    subst'' = subst'
        { substitution =
            sortBy (compare `on` fst) (ExpandedPattern.substitution subst')
        }


andSimplifyFailure
    :: (HasCallStack)
    => String
    -> UnificationTerm Object
    -> UnificationTerm Object
    -> UnificationError
    -> TestTree
andSimplifyFailure message term1 term2 err =
    testCase
        message
        (assertEqualWithPrinter
            prettyPrintToString
            ""
            (Left err)
            ( evalCounter
              . runExceptT
              $ simplifyAnds tools [(unificationProblem term1 term2)]
            )
        )

andSimplifyException
    :: (HasCallStack)
    => String
    -> UnificationTerm Object
    -> UnificationTerm Object
    -> String
    -> TestTree
andSimplifyException message term1 term2 exceptionMessage =
    testCase
        message
        ( catch test handler )
    where
        test = do
            let var =
                    evalCounter
                    . runExceptT
                    $ simplifyAnds tools [(unificationProblem term1 term2)]
            _ <- evaluate (var)
            assertFailure "This evaluation should fail"
        handler (ErrorCall s) =
            assertEqual ""
                exceptionMessage
                s

unificationProcedureSuccess
    :: (HasCallStack)
    => String
    -> UnificationTerm Object
    -> UnificationTerm Object
    -> Substitution Object
    -> Predicate Object Variable
    -> UnificationProof Object Variable
    -> TestTree
unificationProcedureSuccess
    message
    (UnificationTerm term1)
    (UnificationTerm term2)
    subst
    predicate'
    proof
  = testCase
        message
        (assertEqualWithExplanation
            ""
            (unificationSubstitution subst, predicate', proof)
            (sortBy (compare `on` fst) substitution, predicate, proof')
        )
  where
    Right ( PredicateSubstitution.PredicateSubstitution
              { substitution
              , predicate
              }
          , proof'
          ) =
        evalCounter . runExceptT $
            ( unificationProcedure
                tools
                (extractPurePattern term1)
                (extractPurePattern term2)
            )

test_unification :: [TestTree]
test_unification =
    [ andSimplifySuccess "Constant"
        (UnificationTerm aA)
        (UnificationTerm aA)
        (UnificationResultTerm aA)
        []
        makeTruePredicate
        EmptyUnificationProof
    , andSimplifySuccess "Variable"
        (UnificationTerm x)
        (UnificationTerm aA)
        (UnificationResultTerm aA)
        [("x", aA)]
        makeTruePredicate
        EmptyUnificationProof
    , andSimplifySuccess "one level"
        (UnificationTerm (applyS f [x]))
        (UnificationTerm (applyS f [aA]))
        (UnificationResultTerm (applyS f [aA]))
        [("x", aA)]
        makeTruePredicate
        EmptyUnificationProof
    , andSimplifySuccess "equal non-constructor patterns"
        (UnificationTerm a2A)
        (UnificationTerm a2A)
        (UnificationResultTerm a2A)
        []
        makeTruePredicate
        EmptyUnificationProof
    , andSimplifySuccess "variable + non-constructor pattern"
        (UnificationTerm a2A)
        (UnificationTerm x)
        (UnificationResultTerm a2A)
        [("x", a2A)]
        makeTruePredicate
        EmptyUnificationProof
    , andSimplifySuccess
        "https://basics.sjtu.edu.cn/seminars/c_chu/Algorithm.pdf slide 3"
        (UnificationTerm (applyS ef [ex1, applyS eh [ex1], ex2]))
        (UnificationTerm (applyS ef [applyS eg [ex3], ex4, ex3]))
        (UnificationResultTerm
            (applyS ef [applyS eg [ex3], applyS eh [ex1], ex3])
        )
        [ ("ex1", applyS eg [ex3])
        , ("ex2", ex3)
        , ("ex4", applyS eh [applyS eg [ex3]])
        ]
        makeTruePredicate
        EmptyUnificationProof
    , andSimplifySuccess
        "f(g(X),X) = f(Y,a) https://en.wikipedia.org/wiki/Unification_(computer_science)#Examples_of_syntactic_unification_of_first-order_terms"
        (UnificationTerm
            (applyS nonLinF [applyS nonLinG [nonLinX], nonLinX])
        )
        (UnificationTerm (applyS nonLinF [nonLinY, nonLinA]))
        (UnificationResultTerm
            (applyS nonLinF [applyS nonLinG [nonLinX], nonLinA])
        )
        -- [ ("x", nonLinA), ("y", applyS nonLinG [nonLinX])]
        [ ("x", nonLinA)
        , ("y", applyS nonLinG [nonLinA])
        ]
        makeTruePredicate
        EmptyUnificationProof
    , andSimplifySuccess
        "times(times(a, y), x) = times(x, times(y, a))"
        (UnificationTerm (applyS expBin [applyS expBin [expA, expY], expX]))
        (UnificationTerm (applyS expBin [expX, applyS expBin [expY, expA]]))
        (UnificationResultTerm (applyS
            expBin
            [ applyS expBin [expA, expY]
            , applyS expBin [expY, expA]
            ]
        ))
        [ ("a", expY)
        , ("x", applyS expBin [expY, expY])
        ]
        makeTruePredicate
        EmptyUnificationProof
    , unificationProcedureSuccess
        "times(x, g(x)) = times(a, a) -- cycle bottom"
        (UnificationTerm (applyS expBin [expX, applyS eg [expX]]))
        (UnificationTerm (applyS expBin [expA, expA]))
        []
        makeFalsePredicate
        EmptyUnificationProof
    , unificationProcedureSuccess
        "times(times(a, y), x) = times(x, times(y, a))"
        (UnificationTerm (applyS expBin [applyS expBin [expA, expY], expX]))
        (UnificationTerm (applyS expBin [expX, applyS expBin [expY, expA]]))
        [ ("a", expY)
        , ("x", applyS expBin [expY, expY])
        ]
        makeTruePredicate
        EmptyUnificationProof
    , unificationProcedureSuccess
        "Unifying two non-ctors results in equals predicate"
         (UnificationTerm a2A)
         (UnificationTerm a4A)
         []
         (makeEqualsPredicate a2A a4A)
         EmptyUnificationProof
    , unificationProcedureSuccess
        "Unifying function and variable results in ceil predicate"
         (UnificationTerm x)
         (UnificationTerm a5A)
         [ ("x", a5A)
         ]
         (give mockSymbolOrAliasSorts
             $ makeCeilPredicate
             $ extractPurePattern a5A
         )
         EmptyUnificationProof
    , testGroup "inj unification tests" injUnificationTests
    , andSimplifySuccess "Unmatching constants is bottom"
        (UnificationTerm aA)
        (UnificationTerm a1A)
        (UnificationResultTerm bottomPredicate)
        []
        makeFalsePredicate
        EmptyUnificationProof
    , andSimplifySuccess "Unmatching domain values is bottom"
        (UnificationTerm dv1)
        (UnificationTerm dv2)
        (UnificationResultTerm bottomPredicate)
        []
        makeFalsePredicate
        EmptyUnificationProof
    , andSimplifyException "Unmatching constructor constant + domain value"
        (UnificationTerm aA)
        (UnificationTerm dv2)
        "Cannot handle Constructor and DomainValue"
    , andSimplifyException "Unmatching domain value + constructor constant"
        (UnificationTerm dv1)
        (UnificationTerm aA)
        "Cannot handle DomainValue and Constructor"
    , andSimplifySuccess "Unmatching domain value + nonconstructor constant"
        (UnificationTerm dv1)
        (UnificationTerm a2A)
        (UnificationResultTerm dv1)
        []
        (makeEqualsPredicate dv1 a2A)
        EmptyUnificationProof
    , andSimplifySuccess "Unmatching nonconstructor constant + domain value"
        (UnificationTerm a2A)
        (UnificationTerm dv1)
        (UnificationResultTerm a2A)
        []
        (makeEqualsPredicate a2A dv1)
        EmptyUnificationProof
    , andSimplifyFailure "non-functional pattern"
        (UnificationTerm x)
        (UnificationTerm a3A)
        UnsupportedPatterns
    , andSimplifySuccess "non-constructor symbolHead right"
        (UnificationTerm aA)
        (UnificationTerm a2A)
        (UnificationResultTerm aA)
        []
        (makeEqualsPredicate aA a2A)
        EmptyUnificationProof
    , andSimplifySuccess "non-constructor symbolHead left"
        (UnificationTerm a2A)
        (UnificationTerm aA)
        (UnificationResultTerm a2A)
        []
        (makeEqualsPredicate a2A aA)
        EmptyUnificationProof
    , andSimplifySuccess "nested a=a1 is bottom"
        (UnificationTerm (applyS f [aA]))
        (UnificationTerm (applyS f [a1A]))
        (UnificationResultTerm bottomPredicate)
        []
        makeFalsePredicate
        EmptyUnificationProof
    , andSimplifyFailure "Unsupported constructs"
        (UnificationTerm (applyS f [aA]))
        (UnificationTerm (applyS f [implies_ aA (next_ a1A)]))
        UnsupportedPatterns
          {- currently this cannot even be built because of builder checkd
    , andSimplifyFailure "Unmatching sorts"
        (UnificationTerm aA)
        (UnificationTerm bA)
        UnificationError
        -}
    , testCase "Maps substitution variables"
        (assertEqualWithExplanation ""
            [(W "1", war' "2")]
            (mapSubstitutionVariables showVar
                [(V 1, var' 2)]
            )
        )
    ]

newtype V level = V Integer
    deriving (Show, Eq, Ord)
newtype W level = W String
    deriving (Show, Eq, Ord)

instance EqualWithExplanation (V level)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

instance EqualWithExplanation (W level)
  where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show


showVar :: V level -> W level
showVar (V i) = W (show i)

var' :: Integer -> PureMLPattern Meta V
var' i = give mockSymbolOrAliasSorts' (mkVar (V i))

war' :: String -> PureMLPattern Meta W
war' s = give mockSymbolOrAliasSorts' (mkVar (W s))

mockSymbolOrAliasSorts' :: SymbolOrAliasSorts Meta
mockSymbolOrAliasSorts' = const ApplicationSorts
    { applicationSortsOperands = [sortVar, sortVar]
    , applicationSortsResult = sortVar
    }

sortVar :: Sort level
sortVar = SortVariableSort (SortVariable (Id "#a" AstLocationTest))

injUnificationTests :: [TestTree]
injUnificationTests =
    [ andSimplifySuccess "Injected Variable"
        (UnificationTerm (applyInj s1 s2 x))
        (UnificationTerm (applyInj s1 s2 aA))
        (UnificationResultTerm (applyInj s1 s2 aA))
        [("x", aA)]
        makeTruePredicate
        EmptyUnificationProof
    , andSimplifySuccess "Variable"
        (UnificationTerm xs2)
        (UnificationTerm (applyInj s1 s2 aA))
        (UnificationResultTerm (applyInj s1 s2 aA))
        [("xs2", applyInj s1 s2 aA)]
        makeTruePredicate
        EmptyUnificationProof
    , andSimplifySuccess "Injected Variable vs doubly injected term"
        (UnificationTerm (applyInj s1 s2 x))
        (simplifyPattern (UnificationTerm (applyInj s3 s2 (applyInj s1 s3 aA))))
        (UnificationResultTerm (applyInj s1 s2 aA))
        [("x", aA)]
        makeTruePredicate
        EmptyUnificationProof
    , andSimplifySuccess "doubly injected variable vs injected term"
        (simplifyPattern (UnificationTerm (applyInj s3 s2 (applyInj s1 s3 x))))
        (UnificationTerm (applyInj s1 s2 aA))
        (UnificationResultTerm (applyInj s1 s2 aA))
        [("x", aA)]
        makeTruePredicate
        EmptyUnificationProof
    , andSimplifySuccess "doubly injected variable vs doubly injected term"
        (simplifyPattern (UnificationTerm (applyInj s4 s2 (applyInj s1 s4 x))))
        (simplifyPattern (UnificationTerm (applyInj s3 s2 (applyInj s1 s3 aA))))
        (UnificationResultTerm (applyInj s1 s2 aA))
        [("x", aA)]
        makeTruePredicate
        EmptyUnificationProof
    , andSimplifySuccess "constant vs injection is bottom"
        (UnificationTerm aA)
        (UnificationTerm (applyInj s2 s1 xs2))
        (UnificationResultTerm bottomPredicate)
        []
        makeFalsePredicate
        EmptyUnificationProof
    , andSimplifySuccess "unmatching nested injections"
        (simplifyPattern (UnificationTerm (applyInj s2 s4 (applyInj s1 s2 aA))))
        (simplifyPattern (UnificationTerm (applyInj s3 s4 (applyInj s2 s3 bA))))
        (UnificationResultTerm bottomPredicate)
        []
        makeFalsePredicate
        EmptyUnificationProof
    , andSimplifySuccess "unmatching injections"
        -- TODO(traiansf): this should succeed if s1 < s2 < s3
        (UnificationTerm (applyInj s1 s3 aA))
        (UnificationTerm (applyInj s2 s3 xs2))
        (UnificationResultTerm bottomPredicate)
        []
        makeFalsePredicate
        EmptyUnificationProof
    ]

simplifyPattern :: UnificationTerm Object -> UnificationTerm Object
simplifyPattern (UnificationTerm pStub) =
    let pat =
            project
            $ ExpandedPattern.term
            $ evalSimplifier
            $ do
                simplifiedPatterns <-
                    ExpandedPattern.simplify
                        tools
                        (Mock.substitutionSimplifier tools)
                        (Simplifier.create tools functionRegistry)
                        expandedPattern
                case
                    OrOfExpandedPattern.extractPatterns
                        (fst simplifiedPatterns) of
                    [] -> return ExpandedPattern.bottom
                    (config : _) -> return config
        resultSort = getPatternResultSort mockSymbolOrAliasSorts pat
    in UnificationTerm (SortedPatternStub (SortedPattern pat resultSort))
  where
    functionRegistry = Map.empty
    expandedPattern = Predicated
        { term = extractPurePattern pStub
        , predicate = makeTruePredicate
        , substitution = []
        }

makeEqualsPredicate
    :: CommonPurePatternStub Object
    -> CommonPurePatternStub Object
    -> Predicate Object Variable
makeEqualsPredicate t1 t2 =
        give mockSymbolOrAliasSorts
            $ Predicate.makeEqualsPredicate
                (extractPurePattern t1) (extractPurePattern t2)
