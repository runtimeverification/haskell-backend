module Test.Kore.Step.Simplification.DomainValue
    ( test_domainValueSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import qualified Data.Map.Strict as Map
import           Data.Reflection
                 ( give )
import qualified Data.Sequence as Seq

import           Kore.AST.Common
                 ( DomainValue (..), Sort (..) )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkBottom, mkDomainValue, mkStringLiteral )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_ )
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools, SymbolOrAliasSorts )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.DomainValue
                 ( simplify )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_domainValueSimplification :: [TestTree]
test_domainValueSimplification =
    give mockSymbolOrAliasSorts
    [ testCase "DomainValue evaluates to DomainValue"
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ Predicated
                    { term =
                        mkDomainValue
                            testSort
                            (Domain.BuiltinPattern (mkStringLiteral "a"))
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
            )
            (evaluate
                mockMetadataTools
                (DomainValue
                    testSort
                    (Domain.BuiltinPattern (mkStringLiteral "a"))
                )
            )
        )
    , testCase "\\bottom propagates through builtin Map"
        (assertEqualWithExplanation
            "Expected \\bottom to propagate to the top level"
            (OrOfExpandedPattern.make [])
            (evaluate
                mockMetadataTools
                (DomainValue
                    testSort
                    (Domain.BuiltinMap
                        (Map.fromList [(Mock.aConcrete, bottom)])
                    )
                )
            )
        )
    , testCase "\\bottom propagates through builtin List"
        (assertEqualWithExplanation
            "Expected \\bottom to propagate to the top level"
            (OrOfExpandedPattern.make [])
            (evaluate
                mockMetadataTools
                (DomainValue
                    testSort
                    (Domain.BuiltinList (Seq.fromList [bottom]))
                )
            )
        )
    ]
  where
    bottom = OrOfExpandedPattern.make [ExpandedPattern.bottom]

testSort :: Sort Object
testSort =
    case mkBottom :: CommonStepPattern Object of
        Bottom_ sort -> sort
        _ -> error "unexpected"

mockSymbolOrAliasSorts :: SymbolOrAliasSorts Object
mockSymbolOrAliasSorts = Mock.makeSymbolOrAliasSorts []

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools =
    Mock.makeMetadataTools mockSymbolOrAliasSorts [] [] [] []

evaluate
    :: (MetaOrObject Object)
    => MetadataTools Object attrs
    -> DomainValue Object Domain.Builtin (CommonOrOfExpandedPattern Object)
    -> CommonOrOfExpandedPattern Object
evaluate tools domainValue =
    case simplify tools domainValue of
        (result, _proof) -> result
