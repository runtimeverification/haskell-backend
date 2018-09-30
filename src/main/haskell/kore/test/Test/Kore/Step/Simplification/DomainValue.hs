module Test.Kore.Step.Simplification.DomainValue
    ( test_domainValueSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Data.Reflection
       ( give )

import           Kore.AST.Common
                 ( BuiltinDomain (..), DomainValue (..), Sort (..) )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( CommonPurePattern )
import           Kore.ASTUtils.SmartConstructors
                 ( mkBottom, mkDomainValue, mkStringLiteral )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_ )
import           Kore.IndexedModule.MetadataTools
                 ( SymSorts )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..) )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.DomainValue
                 ( simplify )
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( makeSymSorts )

import Test.Kore.Comparators ()
import Test.Tasty.HUnit.Extensions

test_domainValueSimplification :: [TestTree]
test_domainValueSimplification =
    [ testCase "DomainValue evaluates to DomainValue"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term =
                        give mockSymSorts $
                            mkDomainValue
                                testSort
                                (BuiltinDomainPattern (mkStringLiteral "a"))
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ]
            )
            (evaluate
                (DomainValue
                    testSort
                    (BuiltinDomainPattern (mkStringLiteral "a"))
                )
            )
        )
    ]
  where
    mockSymSorts =
        Mock.makeSymSorts []
            :: SymSorts Object

testSort :: Sort Object
testSort =
    case mkBottom of
        Bottom_ sort -> sort
        _ -> error "unexpected"

evaluate
    ::  (MetaOrObject Object)
    => DomainValue Object (BuiltinDomain (CommonPurePattern Meta))
    -> CommonOrOfExpandedPattern Object
evaluate domainValue =
    case simplify domainValue of
        (result, _proof) -> result
