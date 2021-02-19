{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
{-# LANGUAGE Strict #-}

module Kore.Step.Simplification.InjSimplifier
    ( Distinct (..)
    , InjSimplifier (..)
    , mkInjSimplifier
    , normalize
    ) where

import Prelude.Kore

import qualified Data.Functor.Foldable as Recursive
import qualified Data.Set as Set
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Synthetic
    ( synthesize
    )
import Kore.Debug
import Kore.IndexedModule.SortGraph
    ( SortGraph
    , isSubsortOf
    , subsortsOf
    )
import Kore.Internal.Inj
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    )
import Pair

{- | Two 'Inj' are 'Distinct' if they are known not to unify.

Otherwise, 'unifyInj' may return 'Unknown'.

 -}
data Distinct = Distinct | Unknown
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (Hashable)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

data InjSimplifier =
    InjSimplifier
        { isOrderedInj :: forall child. Inj child -> Bool
        -- ^ Is 'injFrom' a proper subsort of 'injTo'?

        , evaluateInj
            :: forall variable
            .  HasCallStack
            => InternalVariable variable
            => Inj (TermLike variable)
            -> TermLike variable
        {- ^ Apply the triangle axiom to combine an 'Inj' with its 'Inj' child:

        @
            inj{middle, outer}(inj{inner, middle}(_)) = inj{inner, outer}(_)
        @
         -}

        , unifyInj
            :: forall variable
            .  InternalVariable variable
            => Inj (TermLike variable)
            -> Inj (TermLike variable)
            -> Either Distinct (Inj (Pair (TermLike variable)))
        {- ^ Push down the conjunction of 'Inj':

        @
            inj{lo, hi}(a) ∧ inj{lower, hi}(b)
            ===
            inj{lo, hi}(a ∧ inj{lower, lo}(b))
                where lower < lo
        @

        Returns 'Distinct' if the sort injections cannot match, or 'Unknown' if
        further simplification could produce matching injections.
         -}

        , evaluateCeilInj
            :: forall variable
            .  HasCallStack
            => InternalVariable variable
            => Ceil Sort (Inj (TermLike variable))
            -> Ceil Sort (TermLike variable)
        {- ^ Evaluate the 'Ceil' of 'Inj':

        @
            \ceil{outer, middle}(inj{inner, middle}(x))
            ===
            \ceil{outer, inner}(x)
                where inner < middle
        @
         -}

        , injectTermTo
            :: forall variable
            .  HasCallStack
            => InternalVariable variable
            => Inj ()
            -> TermLike variable
            -> Sort
            -> TermLike variable
        {- ^ Injects a term to a given sort. Applies 'evaluateInj' to keep
        the injection simplified.
        -}
    }

-- | Ignore 'UnorderedInj' errors in 'evaluateInj' and 'evaluateCeilInj' below.
ignoreUnorderedInj :: Bool
ignoreUnorderedInj =
    -- TODO (thomas.tuegel): Fix the frontend and change to 'False'.
    True

mkInjSimplifier :: SortGraph -> InjSimplifier
mkInjSimplifier sortGraph =
    InjSimplifier
        { evaluateInj, unifyInj, isOrderedInj, evaluateCeilInj, injectTermTo }
  where
    isSubsortOf' = isSubsortOf sortGraph

    isOrderedInj :: forall child. Inj child -> Bool
    isOrderedInj Inj { injFrom, injTo }
      | SortVariableSort _ <- injFrom
      , SortVariableSort _ <- injTo
      =
        -- Assume variable sorts are properly ordered.
        True

      | otherwise = injFrom `isSubsortOf'` injTo

    evaluateInj
        :: forall variable
        .  HasCallStack
        => InternalVariable variable
        => Inj (TermLike variable)
        -> TermLike variable
    evaluateInj inj
      | injFrom inj == injTo inj = injChild inj
      | not ignoreUnorderedInj, not (isOrderedInj inj) = unorderedInj inj
      | otherwise =
        case injChild inj of
            Inj_ inj'
              | not ignoreUnorderedInj, not (isOrderedInj inj') ->
                unorderedInj inj
              | otherwise ->
                assert sameConstructor
                . assert innerSortsAgree
                . synthesize . InjF
                $ Inj
                    { injConstructor = injConstructor inj
                    , injTo = injTo inj
                    , injFrom = injFrom inj'
                    , injChild = injChild inj'
                    , injAttributes = injAttributes inj
                    }
              where
                sameConstructor = injConstructor inj == injConstructor inj'
                innerSortsAgree = injFrom inj == injTo inj'

            _ -> synthesize $ InjF inj

    evaluateCeilInj
        :: forall variable
        .  Ceil Sort (Inj (TermLike variable))
        -> Ceil Sort (TermLike variable)
    evaluateCeilInj Ceil { ceilResultSort, ceilChild = inj }
      | not ignoreUnorderedInj, not (isOrderedInj inj) = unorderedInj inj
      | otherwise =
        Ceil
            { ceilOperandSort = injFrom inj
            , ceilResultSort
            , ceilChild = injChild inj
            }

    unifyInj
        :: forall variable
        .  InternalVariable variable
        => Inj (TermLike variable)
        -> Inj (TermLike variable)
        -> Either Distinct (Inj (Pair (TermLike variable)))
    unifyInj inj1 inj2
      | injTo1 /= injTo2 = Left Distinct

      | injFrom1 == injFrom2 =
        assert (injTo1 == injTo2) $ do
            let child1 = injChild inj1
                child2 = injChild inj2
            pure (Pair child1 child2 <$ inj1)

      | injFrom2 `isSubsortOf'` injFrom1 =
        assert (injTo1 == injTo2) $ do
            let child1' = injChild inj1
                child2' = evaluateInj inj2 { injTo = injFrom1 }
            pure (Pair child1' child2' <$ inj1)

      | injFrom1 `isSubsortOf'` injFrom2 =
        assert (injTo1 == injTo2) $ do
            let child1' = evaluateInj inj1 { injTo = injFrom2 }
                child2' = injChild inj2
            pure (Pair child1' child2' <$ inj2)

      -- If the child patterns are simplifiable, then they could eventually be
      -- simplified to produce matching sort injections, but if they are
      -- non-simplifiable, then they will never match.
      | hasConstructorLikeTop (injChild inj1) = Left Distinct
      | hasConstructorLikeTop (injChild inj2) = Left Distinct

      -- Even if the child patterns are simplifiable, if they do not have any
      -- common subsorts, then they will never simplify to produce matching sort
      -- injections.
      | Set.disjoint subsorts1 subsorts2 = Left Distinct

      | otherwise = Left Unknown
      where
        Inj { injFrom = injFrom1, injTo = injTo1 } = inj1
        Inj { injFrom = injFrom2, injTo = injTo2 } = inj2
        subsorts1 = subsortsOf sortGraph injFrom1
        subsorts2 = subsortsOf sortGraph injFrom2

    injectTermTo injProto injChild injTo =
        evaluateInj injProto { injFrom, injTo, injChild }
      where
        injFrom = termLikeSort injChild

normalize
    :: InjSimplifier
    -> TermLike RewritingVariableName
    -> TermLike RewritingVariableName
normalize InjSimplifier { evaluateInj } =
    Recursive.fold worker
  where
    worker (_ :< termLikeF) =
        case termLikeF of
            InjF inj -> evaluateInj inj
            _ -> synthesize termLikeF
