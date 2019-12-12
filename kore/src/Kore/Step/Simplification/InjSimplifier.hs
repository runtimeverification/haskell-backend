{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Step.Simplification.InjSimplifier
    ( Distinct (..)
    , InjSimplifier (..)
    , mkInjSimplifier
    , simplifyInj
    , embedInj
    , normalize
    ) where

import qualified Control.Exception as Exception
import Data.Bifunctor
    ( bimap
    )
import Data.Function
    ( (&)
    )
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Set as Set
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import qualified GHC.Stack as GHC

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
import Pair

{- | Two 'Inj' are 'Distinct' if they are known not to unify.

Otherwise, 'unifyInj' may return 'Unknown'.

 -}
data Distinct = Distinct | Unknown
    deriving (Eq, Show)
    deriving (GHC.Generic)

instance SOP.Generic Distinct

instance SOP.HasDatatypeInfo Distinct

instance Debug Distinct

instance Diff Distinct

data InjSimplifier =
    InjSimplifier
        { isOrderedInj :: forall child. Inj child -> Bool
        -- ^ Is 'injFrom' a proper subsort of 'injTo'?

        , evaluateInj
            :: forall variable
            .  GHC.HasCallStack
            => InternalVariable variable
            => Inj (Inj (TermLike variable))
            -> Inj (TermLike variable)
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
            .  GHC.HasCallStack
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
        }

-- | Ignore 'UnorderedInj' errors in 'evaluateInj' and 'evaluateCeilInj' below.
ignoreUnorderedInj :: Bool
ignoreUnorderedInj =
    -- TODO (thomas.tuegel): Fix the frontend and change to 'False'.
    True

mkInjSimplifier :: SortGraph -> InjSimplifier
mkInjSimplifier sortGraph =
    InjSimplifier { evaluateInj, unifyInj, isOrderedInj, evaluateCeilInj }
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
        .  GHC.HasCallStack
        => Inj (Inj (TermLike variable))
        -> Inj (TermLike variable)
    evaluateInj inj@Inj { injChild = inj' }
      | not ignoreUnorderedInj, not (isOrderedInj inj) = unorderedInj inj
      | not ignoreUnorderedInj, not (isOrderedInj inj') = unorderedInj inj'
      | otherwise =
        Exception.assert sameConstructor
        . Exception.assert innerSortsAgree
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
        Exception.assert (injTo1 == injTo2) $ do
            let child1 = injChild inj1
                child2 = injChild inj2
            pure (Pair child1 child2 <$ inj1)

      | injFrom2 `isSubsortOf'` injFrom1 =
        Exception.assert (injTo1 == injTo2) $ do
            let child1' = injChild inj1
                child2' = embedInj inj2 { injTo = injFrom1 }
            pure (Pair child1' child2' <$ inj1)

      | injFrom1 `isSubsortOf'` injFrom2 =
        Exception.assert (injTo1 == injTo2) $ do
            let child1' = embedInj inj1 { injTo = injFrom2 }
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

simplifyInj
    :: InternalVariable variable
    => InjSimplifier
    -> Inj (TermLike variable)
    -> TermLike variable
simplifyInj InjSimplifier { evaluateInj } inj@Inj { injChild } =
    case injChild of
        Inj_ inj' -> evaluateInj (inj' <$ inj)
        _ -> inj
    & (synthesize . InjF)

embedInj
    :: InternalVariable variable
    => Inj (TermLike variable)
    -> TermLike variable
embedInj = synthesize . InjF

normalize
    :: forall variable
    .  InternalVariable variable
    => InjSimplifier
    -> TermLike variable
    -> TermLike variable
normalize InjSimplifier { evaluateInj } =
    unwrap . Recursive.fold worker
  where
    unwrap = either embedInj id

    worker
        ::  Recursive.Base
                (TermLike variable)
                (Either (Inj (TermLike variable)) (TermLike variable))
        -> Either (Inj (TermLike variable)) (TermLike variable)
    worker original@(_ :< termLikeF) =
        case termLikeF of
            InjF inj -> Left (either evaluateInj id $ biparallel inj)
            _ -> Right (either embedInj Recursive.embed $ sequence original)

    -- The inverse of 'Data.Bitraversable.bisequence'.
    biparallel
        :: Inj (Either (Inj a) b)
        -> Either (Inj (Inj a)) (Inj b)
    biparallel inj@Inj { injChild } =
        bimap (<$ inj) (<$ inj) $ injChild
