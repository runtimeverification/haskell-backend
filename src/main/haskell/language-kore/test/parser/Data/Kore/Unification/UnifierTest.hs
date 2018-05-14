{-# LANGUAGE FlexibleContexts #-}
module Data.Kore.Unification.UnifierTest where

import           Data.CallStack
import           Test.Tasty                                          (TestTree,
                                                                      testGroup)
import           Test.Tasty.HUnit                                    (testCase)
import           Test.Tasty.HUnit.Extensions

import           Data.Kore.AST.Builders
import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.MLPatterns
import           Data.Kore.AST.PureML
import           Data.Kore.ASTPrettyPrint
import           Data.Kore.ASTVerifier.DefinitionVerifierTestHelpers
import           Data.Kore.Unification.UnifierImpl

import           Data.Fix
import           Data.Function                                       (on)
import           Data.List                                           (sortBy)

s1, s2, s3 :: Sort Object
s1 = simpleSort (SortName "s1")
s2 = simpleSort (SortName "s2")
s3 = simpleSort (SortName "s3")

a, a1, a2, a3, b, c, f, g, h :: PureSentenceSymbol Object
a = symbol_ "a" [] s1
a1 = symbol_ "a1" [] s1
a2 = symbol_ "a2" [] s1
a3 = symbol_ "a3" [] s1
b = symbol_ "b" [] s2
c = symbol_ "c" [] s3
f = symbol_ "f" [s1] s2
g = symbol_ "g" [s1, s2] s3
h = symbol_ "h" [s1, s2, s3] s1

ef, eg, eh :: PureSentenceSymbol Object
ef = symbol_ "ef" [s1, s1, s1] s1
eg = symbol_ "eg" [s1] s1
eh = symbol_ "eh" [s1] s1

nonLinF, nonLinG, nonLinAS :: PureSentenceSymbol Object
nonLinF = symbol_ "nonLinF" [s1, s1] s1
nonLinG = symbol_ "nonLinG" [s1] s1
nonLinAS = symbol_ "nonLinA" [] s1

nonLinA, nonLinX, nonLinY :: CommonPurePatternStub Object
nonLinX = parameterizedVariable_ s1 "x"
nonLinY = parameterizedVariable_ s1 "y"

nonLinA = applyS nonLinAS []

expBin :: PureSentenceSymbol Object
expBin = symbol_ "times" [s1, s1] s1

expA, expX, expY, expZ, expW :: CommonPurePatternStub Object
expA = parameterizedVariable_ s1 "a"
expX = parameterizedVariable_ s1 "x"
expY = parameterizedVariable_ s1 "y"
expZ = parameterizedVariable_ s1 "z"
expW = parameterizedVariable_ s1 "w"

ex1, ex2, ex3, ex4 :: CommonPurePatternStub Object
ex1 = parameterizedVariable_ s1 "ex1"
ex2 = parameterizedVariable_ s1 "ex2"
ex3 = parameterizedVariable_ s1 "ex3"
ex4 = parameterizedVariable_ s1 "ex4"

aA :: CommonPurePatternStub Object
aA = applyS a []

a1A :: CommonPurePatternStub Object
a1A = applyS a1 []

nextA1 :: CommonPurePatternStub Object
nextA1 = next_ a1A

aImpliesXa1 :: CommonPurePatternStub Object
aImpliesXa1 = implies_ aA nextA1

faImpliesXa1 :: CommonPurePatternStub Object
faImpliesXa1 = applyS f [aImpliesXa1]

a2A :: CommonPurePatternStub Object
a2A = applyS a2 []

a3A :: CommonPurePatternStub Object
a3A = applyS a3 []

bA :: CommonPurePatternStub Object
bA = applyS b []

x :: CommonPurePatternStub Object
x = parameterizedVariable_ s1 "x"

fx :: CommonPurePatternStub Object
fx = applyS f [x]

fa :: CommonPurePatternStub Object
fa = applyS f [aA]

fa1 :: CommonPurePatternStub Object
fa1 = applyS f [a1A]

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
    , getArgumentSorts = mockGetArgumentSorts
    , getResultSort = mockGetResultSort
    }

extractPurePattern
    :: MetaOrObject level
    => CommonPurePatternStub level -> CommonPurePattern level
extractPurePattern (SortedPatternStub sp) =
    asPurePattern $ sortedPatternPattern sp
extractPurePattern (UnsortedPatternStub ups) =
    error ("Cannot find a sort for "
        ++ show (ups (dummySort (undefined :: level))))

unificationProblem
    :: MetaOrObject level
    => CommonPurePatternStub level
    -> CommonPurePatternStub level
    -> CommonPurePattern level
unificationProblem term1 term2 = extractPurePattern (and_ term1 term2)

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
                    getPatternResultSort mockGetResultSort (unFix pp)
                , variableName = Id v
                }
            , pp
            )

unificationResult
    :: CommonPurePatternStub Object
    -> Substitution Object
    -> UnificationSolution Object
unificationResult pat sub = UnificationSolution
    { unificationSolutionTerm = extractPurePattern pat
    , unificationSolutionConstraints = unificationSubstitution sub
    }

unificationSuccess
    :: (HasCallStack)
    => String
    -> CommonPurePatternStub Object
    -> CommonPurePatternStub Object
    -> CommonPurePatternStub Object
    -> Substitution Object
    -> UnificationProof Object
    -> TestTree
unificationSuccess message term1 term2 term subst proof =
    testCase
        message
        (assertEqualWithPrinter
            prettyPrintToString
            ""
            (unificationResult term subst, proof)
            (subst'', proof')
        )
  where
    Right (subst', proof') = simplifyAnd tools (unificationProblem term1 term2)
    subst'' = subst'
        { unificationSolutionConstraints =
            sortBy (compare `on` fst) (unificationSolutionConstraints subst')
        }


unificationFailure
    :: (HasCallStack)
    => String
    -> CommonPurePatternStub Object
    -> CommonPurePatternStub Object
    -> UnificationError Object
    -> TestTree
unificationFailure message term1 term2 err =
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
    -> CommonPurePatternStub Object
    -> CommonPurePatternStub Object
    -> Substitution Object
    -> UnificationProof Object
    -> TestTree
unificationProcedureSuccess message term1 term2 subst proof =
    testCase
        message
        (assertEqualWithPrinter
            prettyPrintToString
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

unificationProcedureFailure
    :: (HasCallStack)
    => String
    -> CommonPurePatternStub Object
    -> CommonPurePatternStub Object
    -> UnificationError Object
    -> TestTree
unificationProcedureFailure message term1 term2 err =
    testCase
        message
        (assertEqualWithPrinter
            prettyPrintToString
            ""
            (Left err)
            (unificationProcedure
                tools
                (extractPurePattern term1)
                (extractPurePattern term2)
            )
        )

unificationTests :: TestTree
unificationTests =
    testGroup
        "Unification Tests"
        [ unificationSuccess "Constant"
            aA
            aA
            aA
            []
            (ConjunctionIdempotency (extractPurePattern aA))
        , unificationSuccess "Variable"
            x
            aA
            aA
            [("x", aA)]
            (Proposition_5_24_3
                [FunctionalHead (symbolHead a)]
                (var x)
                (extractPurePattern aA)
            )
        , unificationSuccess "one level"
            fx
            fa
            fa
            [("x", aA)]
            (AndDistributionAndConstraintLifting
                (getSentenceSymbolOrAliasHead f [])
                [ Proposition_5_24_3
                    [FunctionalHead (symbolHead a)]
                    (var x)
                    (extractPurePattern aA)
                ]
            )
        , unificationSuccess "equal non-constructor patterns"
            a2A
            a2A
            a2A
            []
            (ConjunctionIdempotency (extractPurePattern a2A))
        , unificationSuccess "variable + non-constructor pattern"
            a2A
            x
            a2A
            [("x", a2A)]
            (Proposition_5_24_3
                [FunctionalHead (symbolHead a2)]
                (var x)
                (extractPurePattern a2A)
            )
        , unificationSuccess
            "https://basics.sjtu.edu.cn/seminars/c_chu/Algorithm.pdf slide 3"
            (applyS ef [ex1, applyS eh [ex1], ex2])
            (applyS ef [applyS eg [ex3], ex4, ex3])
            (applyS ef [applyS eg [ex3], applyS eh [ex1], ex3])
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
        , unificationSuccess
            "f(g(X),X) = f(Y,a) https://en.wikipedia.org/wiki/Unification_(computer_science)#Examples_of_syntactic_unification_of_first-order_terms"
            (applyS nonLinF [applyS nonLinG [nonLinX], nonLinX])
            (applyS nonLinF [nonLinY, nonLinA])
            (applyS nonLinF [applyS nonLinG [nonLinX], nonLinA])
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
        , unificationSuccess
            "times(times(a, y), x) = times(x, times(y, a))"
            (applyS expBin [applyS expBin [expA, expY], expX])
            (applyS expBin [expX, applyS expBin [expY, expA]])
            (applyS
                expBin
                [ applyS expBin [expA, expY]
                , applyS expBin [expY, expA]
                ]
            )
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
            "times(times(a, y), x) = times(x, times(y, a))"
            (applyS expBin [applyS expBin [expA, expY], expX])
            (applyS expBin [expX, applyS expBin [expY, expA]])
            [ ("a", expY)
            , ("x", applyS expBin [expY, expA])
            , ("y", expA)
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
                , CombinedUnificationProof
                    [ CombinedUnificationProof
                        [ CombinedUnificationProof
                            [ EmptyUnificationProof
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
                            ]
                        , EmptyUnificationProof
                        ]
                    , EmptyUnificationProof
                    ]
                ]
            )
         , unificationFailure "Unmatching constants"
            aA
            a1A
            (ConstructorClash (symbolHead a) (symbolHead a1))
        , unificationFailure "non-functional pattern"
            x
            a3A
            NonFunctionalPattern
        , unificationFailure "non-constructor symbolHead right"
            aA
            a2A
            (NonConstructorHead (symbolHead a2))
        , unificationFailure "non-constructor symbolHead left"
            a2A
            aA
            (NonConstructorHead (symbolHead a2))
        , unificationFailure "nested failure"
            fa
            fa1
            (ConstructorClash (symbolHead a) (symbolHead a1))
        , unificationFailure "Unsupported constructs"
            fa
            faImpliesXa1
            UnsupportedPatterns
             {- currently this cannot even be built because of builder checkd
        , unificationFailure "Unmatching sorts"
            aA
            bA
            UnificationError
            -}
        ]
  where
    symbolHead symbol = getSentenceSymbolOrAliasHead symbol []
    var ps = case unFix (extractPurePattern ps) of
        VariablePattern v -> v
