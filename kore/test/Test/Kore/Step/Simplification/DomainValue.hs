module Test.Kore.Step.Simplification.DomainValue
    ( test_domainValueSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.Representation.ExpandedPattern
                 ( Predicated (..) )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make )
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import           Kore.Step.Simplification.DomainValue
                 ( simplify )

import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
import           Test.Kore.Step.MockSymbols
                 ( testSort )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_domainValueSimplification :: [TestTree]
test_domainValueSimplification =
    [ testCase "DomainValue evaluates to DomainValue"
        (assertEqualWithExplanation ""
            (MultiOr.make
                [ Predicated
                    { term =
                        mkDomainValue
                            (Domain.BuiltinExternal Domain.External
                                { domainValueSort = testSort
                                , domainValueChild =
                                    eraseAnnotations $ mkStringLiteral "a"
                                }
                            )
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                ]
            )
            (evaluate
                mockMetadataTools
                (Domain.BuiltinExternal Domain.External
                    { domainValueSort = testSort
                    , domainValueChild =
                        eraseAnnotations $ mkStringLiteral "a"
                    }
                )
            )
        )
    , testCase "\\bottom propagates through builtin Map"
        (assertEqualWithExplanation
            "Expected \\bottom to propagate to the top level"
            (MultiOr.make [])
            (evaluate
                mockMetadataTools
                (mkMapDomainValue [(Mock.aConcrete, bottom)])
            )
        )
    , testCase "\\bottom propagates through builtin List"
        (assertEqualWithExplanation
            "Expected \\bottom to propagate to the top level"
            (MultiOr.make [])
            (evaluate
                mockMetadataTools
                (mkListDomainValue [bottom])
            )
        )
    ]
  where
    bottom = MultiOr.make [ExpandedPattern.bottom]

mkMapDomainValue
    :: [(Domain.Key, child)]
    -> Domain.Builtin child
mkMapDomainValue children =
    Domain.BuiltinMap Domain.InternalMap
        { builtinMapSort = Mock.mapSort
        , builtinMapUnit = Mock.unitMapSymbol
        , builtinMapElement = Mock.elementMapSymbol
        , builtinMapConcat = Mock.concatMapSymbol
        , builtinMapChild = Map.fromList children
        }

mkListDomainValue :: [child] -> Domain.Builtin child
mkListDomainValue children =
    Domain.BuiltinList Domain.InternalList
        { builtinListSort = Mock.listSort
        , builtinListUnit = Mock.unitListSymbol
        , builtinListElement = Mock.elementListSymbol
        , builtinListConcat = Mock.concatListSymbol
        , builtinListChild = Seq.fromList children
        }

mockMetadataTools :: MetadataTools Object StepperAttributes
mockMetadataTools = Mock.makeMetadataTools [] [] [] []

evaluate
    :: (MetaOrObject Object)
    => MetadataTools Object attrs
    -> Domain.Builtin (CommonOrOfExpandedPattern Object)
    -> CommonOrOfExpandedPattern Object
evaluate tools domainValue =
    case simplify tools domainValue of
        (result, _proof) -> result
