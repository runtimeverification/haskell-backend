module Test.Data.Kore.Unification.Unifier (test_unification) where

import           Data.CallStack
import           Test.Tasty                                          (TestTree)
import           Test.Tasty.HUnit                                    (testCase)
import           Test.Tasty.HUnit.Extensions

import           Test.Data.Kore
import           Test.Data.Kore.AST.MLPatterns                       (extractPurePattern)
import           Test.Data.Kore.ASTVerifier.DefinitionVerifier
import           Test.Data.Kore.Comparators                          ()

import           Data.Kore.AST.Builders
import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.MLPatterns
import           Data.Kore.AST.PureML
import           Data.Kore.AST.Sentence
import           Data.Kore.ASTPrettyPrint
import           Data.Kore.IndexedModule.MetadataTools
import           Data.Kore.Unification.Error
import           Data.Kore.Unification.UnifierImpl

import           Data.Functor.Foldable
import           Data.Function                                       (on)
import           Data.List                                           (sortBy)

s1, s2, s3 :: Sort Object
s1 = simpleSort (SortName "s1")
s2 = simpleSort (SortName "s2")
s3 = simpleSort (SortName "s3")

a, a1, a2, a3, b, c, f, g, h :: PureSentenceSymbol Object
a = symbol_ "a" AstLocationTest [] s1
a1 = symbol_ "a1" AstLocationTest [] s1
a2 = symbol_ "a2" AstLocationTest [] s1
a3 = symbol_ "a3" AstLocationTest [] s1
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

aA :: CommonPurePatternStub Object
aA = applyS a []

a1A :: CommonPurePatternStub Object
a1A = applyS a1 []

a2A :: CommonPurePatternStub Object
a2A = applyS a2 []

a3A :: CommonPurePatternStub Object
a3A = applyS a3 []

x :: CommonPurePatternStub Object
x = parameterizedVariable_ s1 "x" AstLocationTest

symbols :: [(SymbolOrAlias Object, PureSentenceSymbol Object)]
symbols =
    map
        (\s -> (getSentenceSymbolOrAliasHead s [], s))
        [ a, a1, a2, a3, b, c, f, g, h
        , ef, eg, eh
        , nonLinF, nonLinG, nonLinAS
        , expBin
        ]

mockIsConstructor, mockIsFunctional :: SymbolOrAlias Object -> Bool
mockIsConstructor patternHead
    | patternHead == getSentenceSymbolOrAliasHead a2 [] = False
mockIsConstructor _ = True
mockIsFunctional patternHead
    | patternHead == getSentenceSymbolOrAliasHead a3 [] = False
mockIsFunctional _ = True

mockGetArgumentSorts :: SymbolOrAlias Object -> [Sort Object]
mockGetArgumentSorts patternHead =
    maybe
        (error ("Unexpected Head " ++  show patternHead))
        getSentenceSymbolOrAliasArgumentSorts
        (lookup patternHead symbols)

mockGetResultSort :: SymbolOrAlias Object -> Sort Object
mockGetResultSort patternHead =
    maybe
        (error ("Unexpected Head " ++  show patternHead))
        getSentenceSymbolOrAliasResultSort
        (lookup patternHead symbols)

tools :: MetadataTools Object
tools = MetadataTools
    { isConstructor = mockIsConstructor
    , isFunctional = mockIsFunctional
    , isFunction = const False
    , getArgumentSorts = mockGetArgumentSorts
    , getResultSort = mockGetResultSort
    }

unificationProblem
    :: MetaOrObject level
    => UnificationTerm level
    -> UnificationTerm level
    -> CommonPurePattern level
unificationProblem (UnificationTerm term1) (UnificationTerm term2) =
    extractPurePattern (and_ term1 term2)

type Substitution level =  [(String, CommonPurePatternStub level)]

unificationSubstitution
    :: Substitution Object
    -> [ (Variable Object, CommonPurePattern Object) ]
unificationSubstitution = map trans
  where
    trans (v, p) =
        let pp = extractPurePattern p in
            ( Variable
                { variableSort =
                    getPatternResultSort mockGetResultSort (project pp)
                , variableName = testId v
                }
            , pp
            )

unificationResult
    :: UnificationResultTerm Object
    -> Substitution Object
    -> UnificationSolution Object Variable
unificationResult (UnificationResultTerm pat) sub = UnificationSolution
    { unificationSolutionTerm = extractPurePattern pat
    , unificationSolutionConstraints = unificationSubstitution sub
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
    -> UnificationProof Object Variable
    -> TestTree
andSimplifySuccess message term1 term2 resultTerm subst proof =
    testCase
        message
        (assertEqualWithExplanation
            ""
            (unificationResult resultTerm subst, proof)
            (subst'', proof')
        )
  where
    Right (subst', proof') = simplifyAnd tools (unificationProblem term1 term2)
    subst'' = subst'
        { unificationSolutionConstraints =
            sortBy (compare `on` fst) (unificationSolutionConstraints subst')
        }


andSimplifyFailure
    :: (HasCallStack)
    => String
    -> UnificationTerm Object
    -> UnificationTerm Object
    -> UnificationError Object
    -> TestTree
andSimplifyFailure message term1 term2 err =
    testCase
        message
        (assertEqualWithPrinter
            prettyPrintToString
            ""
            (Left err)
            (simplifyAnd tools (unificationProblem term1 term2))
        )

unificationProcedureSuccess
    :: (HasCallStack)
    => String
    -> UnificationTerm Object
    -> UnificationTerm Object
    -> Substitution Object
    -> UnificationProof Object Variable
    -> TestTree
unificationProcedureSuccess
    message
    (UnificationTerm term1)
    (UnificationTerm term2)
    subst
    proof
  = testCase
        message
        (assertEqualWithExplanation
            ""
            (unificationSubstitution subst, proof)
            (sortBy (compare `on` fst) subst', proof')
        )
  where
    Right (subst', proof') =
        unificationProcedure
            tools
            (extractPurePattern term1)
            (extractPurePattern term2)

test_unification :: [TestTree]
test_unification =
    [ andSimplifySuccess "Constant"
        (UnificationTerm aA)
        (UnificationTerm aA)
        (UnificationResultTerm aA)
        []
        (ConjunctionIdempotency (extractPurePattern aA))
    , andSimplifySuccess "Variable"
        (UnificationTerm x)
        (UnificationTerm aA)
        (UnificationResultTerm aA)
        [("x", aA)]
        (Proposition_5_24_3
            [FunctionalHead (symbolHead a)]
            (var x)
            (extractPurePattern aA)
        )
    , andSimplifySuccess "one level"
        (UnificationTerm (applyS f [x]))
        (UnificationTerm (applyS f [aA]))
        (UnificationResultTerm (applyS f [aA]))
        [("x", aA)]
        (AndDistributionAndConstraintLifting
            (getSentenceSymbolOrAliasHead f [])
            [ Proposition_5_24_3
                [FunctionalHead (symbolHead a)]
                (var x)
                (extractPurePattern aA)
            ]
        )
    , andSimplifySuccess "equal non-constructor patterns"
        (UnificationTerm a2A)
        (UnificationTerm a2A)
        (UnificationResultTerm a2A)
        []
        (ConjunctionIdempotency (extractPurePattern a2A))
    , andSimplifySuccess "variable + non-constructor pattern"
        (UnificationTerm a2A)
        (UnificationTerm x)
        (UnificationResultTerm a2A)
        [("x", a2A)]
        (Proposition_5_24_3
            [FunctionalHead (symbolHead a2)]
            (var x)
            (extractPurePattern a2A)
        )
    , andSimplifySuccess
        "https://basics.sjtu.edu.cn/seminars/c_chu/Algorithm.pdf slide 3"
        (UnificationTerm (applyS ef [ex1, applyS eh [ex1], ex2]))
        (UnificationTerm (applyS ef [applyS eg [ex3], ex4, ex3]))
        (UnificationResultTerm
            (applyS ef [applyS eg [ex3], applyS eh [ex1], ex3])
        )
        [ ("ex1", applyS eg [ex3])
        , ("ex2", ex3)
        , ("ex4", applyS eh [ex1])
        ]
        (AndDistributionAndConstraintLifting
            (getSentenceSymbolOrAliasHead ef [])
            [ Proposition_5_24_3
                [ FunctionalHead (symbolHead eg)
                , FunctionalVariable (var ex3)
                ]
                (var ex1)
                (extractPurePattern $ applyS eg [ex3])
            , Proposition_5_24_3
                [ FunctionalHead (symbolHead eh)
                , FunctionalVariable (var ex1)
                ]
                (var ex4)
                (extractPurePattern $ applyS eh [ex1])
            , Proposition_5_24_3
                [FunctionalVariable (var ex3)]
                (var ex2)
                (extractPurePattern ex3)
            ]
        )
    , andSimplifySuccess
        "f(g(X),X) = f(Y,a) https://en.wikipedia.org/wiki/Unification_(computer_science)#Examples_of_syntactic_unification_of_first-order_terms"
        (UnificationTerm
            (applyS nonLinF [applyS nonLinG [nonLinX], nonLinX])
        )
        (UnificationTerm (applyS nonLinF [nonLinY, nonLinA]))
        (UnificationResultTerm
            (applyS nonLinF [applyS nonLinG [nonLinX], nonLinA])
        )
        [ ("x", nonLinA), ("y", applyS nonLinG [nonLinX])]
        (AndDistributionAndConstraintLifting
            (symbolHead nonLinF)
            [ Proposition_5_24_3
                [ FunctionalHead (symbolHead nonLinG)
                , FunctionalVariable (var nonLinX)
                ]
                (var nonLinY)
                (extractPurePattern (applyS nonLinG [nonLinX]))
            , Proposition_5_24_3
                [ FunctionalHead (symbolHead nonLinAS) ]
                (var nonLinX)
                (extractPurePattern nonLinA)
            ]
        )
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
        [ ("x", applyS expBin [expA, expY])
        , ("x", applyS expBin [expY, expA])
        ]
        (AndDistributionAndConstraintLifting
            (symbolHead expBin)
            [ Proposition_5_24_3
                [ FunctionalHead (symbolHead expBin)
                , FunctionalVariable (var expA)
                , FunctionalVariable (var expY)
                ]
                (var expX)
                (extractPurePattern (applyS expBin [expA, expY]))
            , Proposition_5_24_3
                [ FunctionalHead (symbolHead expBin)
                , FunctionalVariable (var expY)
                , FunctionalVariable (var expA)
                ]
                (var expX)
                (extractPurePattern (applyS expBin [expY, expA]))
            ]
        )
    , unificationProcedureSuccess
        "times(x, g(x)) = times(a, a) -- cycles are resolved elsewhere"
        (UnificationTerm (applyS expBin [expX, applyS eg [expX]]))
        (UnificationTerm (applyS expBin [expA, expA]))
        [ ("a", applyS eg [expX])
        , ("x", applyS eg [expX])
        ]
        (CombinedUnificationProof
            [ AndDistributionAndConstraintLifting
                (symbolHead expBin)
                [ Proposition_5_24_3
                    [ FunctionalVariable (var expA)
                    ]
                    (var expX)
                    (extractPurePattern expA)
                , Proposition_5_24_3
                    [ FunctionalHead (symbolHead eg)
                    , FunctionalVariable (var expX)
                    ]
                    (var expA)
                    (extractPurePattern (applyS eg [expX]))
                ]
            , Proposition_5_24_3
                [ FunctionalHead (symbolHead eg)
                , FunctionalVariable (var expX)
                ]
                (var expX)
                (extractPurePattern (applyS eg [expX]))
            ]
        )
    , unificationProcedureSuccess
        "times(times(a, y), x) = times(x, times(y, a))"
        (UnificationTerm (applyS expBin [applyS expBin [expA, expY], expX]))
        (UnificationTerm (applyS expBin [expX, applyS expBin [expY, expA]]))
        [ ("a", expY)
        , ("x", applyS expBin [expY, expA])
        ]
        (CombinedUnificationProof
            [ AndDistributionAndConstraintLifting
                (symbolHead expBin)
                [ Proposition_5_24_3
                    [ FunctionalHead (symbolHead expBin)
                    , FunctionalVariable (var expA)
                    , FunctionalVariable (var expY)
                    ]
                    (var expX)
                    (extractPurePattern (applyS expBin [expA, expY]))
                , Proposition_5_24_3
                    [ FunctionalHead (symbolHead expBin)
                    , FunctionalVariable (var expY)
                    , FunctionalVariable (var expA)
                    ]
                    (var expX)
                    (extractPurePattern (applyS expBin [expY, expA]))
                ]
            , AndDistributionAndConstraintLifting
                (symbolHead expBin)
                [ Proposition_5_24_3
                    [FunctionalVariable (var expY)]
                    (var expA)
                    (extractPurePattern expY)
                , Proposition_5_24_3
                    [FunctionalVariable (var expA)]
                    (var expY)
                    (extractPurePattern expA)
                ]
            , ConjunctionIdempotency
                (extractPurePattern expY)
            ]
        )
      , andSimplifyFailure "Unmatching constants"
        (UnificationTerm aA)
        (UnificationTerm a1A)
        (ConstructorClash (symbolHead a) (symbolHead a1))
    , andSimplifyFailure "non-functional pattern"
        (UnificationTerm x)
        (UnificationTerm a3A)
        NonFunctionalPattern
    , andSimplifyFailure "non-constructor symbolHead right"
        (UnificationTerm aA)
        (UnificationTerm a2A)
        (NonConstructorHead (symbolHead a2))
    , andSimplifyFailure "non-constructor symbolHead left"
        (UnificationTerm a2A)
        (UnificationTerm aA)
        (NonConstructorHead (symbolHead a2))
    , andSimplifyFailure "nested failure"
        (UnificationTerm (applyS f [aA]))
        (UnificationTerm (applyS f [a1A]))
        (ConstructorClash (symbolHead a) (symbolHead a1))
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
    ]
  where
    symbolHead symbol = getSentenceSymbolOrAliasHead symbol []
    var ps = case project (extractPurePattern ps) of
        VariablePattern v -> v
        _                 -> error "Expecting a variable"
