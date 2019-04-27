{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Pattern.Or
    ( Conditional
    , Pattern
    , PredicateSubstitution
    , fromPatterns
    , fromPattern
    , fromTermLike
    , isFalse
    , isTrue
    , toExpandedPattern
    , toTermLike
    , toPredicate
    ) where

import qualified Data.Foldable as Foldable

import           Kore.AST.MetaOrObject
import           Kore.AST.Valid
import qualified Kore.Predicate.Predicate as Predicate
import qualified Kore.Step.Conditional as Conditional
import qualified Kore.Step.Pattern as Pattern
import           Kore.Step.Representation.MultiOr
                 ( MultiOr )
import qualified Kore.Step.Representation.MultiOr as MultiOr
import qualified Kore.Step.Representation.PredicateSubstitution as PredicateSubstitution
import           Kore.Step.TermLike
import           Kore.TopBottom
                 ( TopBottom (..) )
import           Kore.Unparser

{-| The disjunction of 'Conditional'.
-}
type Conditional level variable term =
    MultiOr (Conditional.Conditional level variable term)

{-| The disjunction of 'Pattern'.
-}
type Pattern level variable = MultiOr (Pattern.Pattern level variable)

{-| The disjunction of 'PredicateSubstitution.PredicateSubstitution'.
-}
type PredicateSubstitution level variable =
    MultiOr (PredicateSubstitution.PredicateSubstitution level variable)

{-| The disjunction of 'Predicate'.
-}
type Predicate variable = MultiOr (Predicate.Predicate variable)

{- | A "disjunction" of one 'Pattern.Pattern'.
 -}
fromPattern
    :: Ord (variable Object)
    => Pattern.Pattern Object variable
    -> Pattern Object variable
fromPattern = MultiOr.singleton

{- | Disjoin a collection of patterns.
 -}
fromPatterns
    :: (Foldable f, Ord (variable Object))
    => f (Pattern.Pattern Object variable)
    -> Pattern Object variable
fromPatterns = MultiOr.make . Foldable.toList

{- | A "disjunction" of one 'TermLike'.

See also: 'fromPattern'

 -}
fromTermLike
    :: Ord (variable Object)
    => TermLike variable
    -> Pattern Object variable
fromTermLike = fromPattern . Pattern.fromTermLike

{-| 'isFalse' checks if the 'Or' is composed only of bottom items.
-}
isFalse
    :: (Ord term, TopBottom term)
    => MultiOr term
    -> Bool
isFalse patt =
    isBottom (MultiOr.make (MultiOr.extractPatterns patt))

{-| 'isTrue' checks if the 'Or' has a single top pattern.
-}
isTrue
    :: (Ord term, TopBottom term)
    => MultiOr term
    -> Bool
isTrue = isTop

{-| 'toExpandedPattern' transforms an 'Pattern' into
an 'Pattern.Pattern'.
-}
toExpandedPattern
    ::  ( SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => Pattern Object variable -> Pattern.Pattern Object variable
toExpandedPattern multiOr
  =
    case MultiOr.extractPatterns multiOr of
        [] -> Pattern.bottom
        [patt] -> patt
        patts ->
            Conditional.Conditional
                { term = Foldable.foldr1 mkOr (Pattern.toMLPattern <$> patts)
                , predicate = Predicate.makeTruePredicate
                , substitution = mempty
                }

{-| Transforms a 'Pattern' into a 'TermLike'.
-}
toTermLike
    ::  ( SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => Pattern Object variable -> TermLike variable
toTermLike multiOr =
    case MultiOr.extractPatterns multiOr of
        [] -> mkBottom_
        [patt] -> Pattern.toMLPattern patt
        patts -> Foldable.foldr1 mkOr (Pattern.toMLPattern <$> patts)

{-| Transforms an 'Predicate' into a 'Predicate.Predicate'. -}
toPredicate
    ::  ( SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => Predicate variable -> Predicate.Predicate variable
toPredicate multiOr =
    Predicate.makeMultipleOrPredicate (MultiOr.extractPatterns multiOr)
