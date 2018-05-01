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
import           Data.Kore.AST.PureML
import           Data.Kore.ASTPrettyPrint
import           Data.Kore.ASTVerifier.DefinitionVerifierTestHelpers
import           Data.Kore.Unification.Unifier

s1, s2, s3 :: Sort Object
s1 = simpleSort (SortName "s1")
s2 = simpleSort (SortName "s2")
s3 = simpleSort (SortName "s3")

a, b, c, f, g, h :: PureSentenceSymbol Object
a = symbol_ "a" [] s1
b = symbol_ "b" [] s2
c = symbol_ "c" [] s3
f = symbol_ "f" [s1] s2
g = symbol_ "g" [s1, s2] s3
h = symbol_ "h" [s1, s2, s3] s1

aA :: CommonPurePatternStub Object
aA = applyS a []


symbols :: [(SymbolOrAlias Object, PureSentenceSymbol Object)]
symbols =
    map
        (\s -> (getSentenceSymbolOrAliasHead s [], s))
        [a, b, c, f, g, h]

mockIsConstructor, mockIsFunctional :: SymbolOrAlias Object -> Bool
mockIsConstructor = const True
mockIsFunctional = const True

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
    :: MetaOrObject level => CommonPurePatternStub level -> CommonPurePattern level
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
    :: MetaOrObject level => Substitution level -> CommonPurePatternStub level
unificationSubstitution = foldr (and_ . eq) top_
  where eq (var, p) = equals_ (unparameterizedVariable_ var) p

unificationResult
    :: MetaOrObject level
    => CommonPurePatternStub level
    -> Substitution level
    -> CommonPurePattern level
unificationResult pat sub =
    extractPurePattern (and_ pat (unificationSubstitution sub))

unificationTest
    :: (HasCallStack)
    => String
    -> CommonPurePatternStub Object
    -> CommonPurePatternStub Object
    -> CommonPurePatternStub Object
    -> Substitution Object
    -> TestTree
unificationTest message term1 term2 term subst =
    testCase
        message
        (assertEqualWithPrinter
            prettyPrintToString
            ""
            (unificationResult term subst)
            (simplifyAnd tools (unificationProblem term1 term2))
        )


unificationTests :: TestTree
unificationTests =
    testGroup
        "Unification Tests"
        [ unificationTest "Constant"
            aA
            aA
            aA
            []
        ]
