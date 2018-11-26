module Test.Kore.Step.OrOfExpandedPattern where

import Test.Tasty.QuickCheck

import Kore.AST.MetaOrObject
import Kore.Predicate.Predicate
import Kore.Step.ExpandedPattern
import Kore.Step.OrOfExpandedPattern

import Test.Kore

expandedPatternGen
    :: MetaOrObject level
    => level
    -> Gen (CommonExpandedPattern level)
expandedPatternGen level = do
    term <- stepPatternGen level
    return Predicated
        { term
        , predicate = makeTruePredicate
        , substitution = mempty
        }

orOfExpandedPatternGen
    :: MetaOrObject level
    => level
    -> Gen (CommonOrOfExpandedPattern level)
orOfExpandedPatternGen level =
    filterOr . MultiOr <$> listOf (expandedPatternGen level)

-- | Check that 'merge' preserves the @\\or@-idempotency condition.
prop_mergeIdemOr :: Gen Property
prop_mergeIdemOr = do
    ors <- orOfExpandedPatternGen Object
    return (merge ors ors === ors)

prop_makeIdemOr :: Gen Property
prop_makeIdemOr = do
    pat <- expandedPatternGen Object
    return (make [pat, pat] === make [pat])

prop_flattenIdemOr :: Gen Property
prop_flattenIdemOr = do
    ors <- orOfExpandedPatternGen Object
    let nested = MultiOr [ors, ors]
    return (flatten nested === ors)
