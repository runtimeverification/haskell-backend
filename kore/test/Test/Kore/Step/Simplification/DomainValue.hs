module Test.Kore.Step.Simplification.DomainValue
    ( test_domainValueSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq

import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern
                 ( Conditional (..) )
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.Simplification.DomainValue
                 ( simplify )

import           Test.Kore.Comparators ()
import           Test.Kore.Step.MockSymbols
                 ( testSort )
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_domainValueSimplification :: [TestTree]
test_domainValueSimplification =
    [ testCase "DomainValue evaluates to DomainValue"
        (assertEqualWithExplanation ""
            (OrPattern.fromPatterns
                [ Conditional
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
                Mock.emptyMetadataTools
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
            (OrPattern.fromPatterns [])
            (evaluate
                Mock.emptyMetadataTools
                (mkMapDomainValue [(Mock.aConcrete, bottom)])
            )
        )
    , testCase "\\bottom propagates through builtin List"
        (assertEqualWithExplanation
            "Expected \\bottom to propagate to the top level"
            (OrPattern.fromPatterns [])
            (evaluate
                Mock.emptyMetadataTools
                (mkListDomainValue [bottom])
            )
        )
    ]
  where
    bottom = OrPattern.fromPatterns [Pattern.bottom]

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

evaluate
    :: SmtMetadataTools attrs
    -> Domain.Builtin (OrPattern Variable)
    -> OrPattern Variable
evaluate = simplify
