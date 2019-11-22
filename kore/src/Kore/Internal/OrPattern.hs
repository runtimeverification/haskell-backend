{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Internal.OrPattern
    ( OrPattern
    , coerceSort
    , isSimplified
    , fromPatterns
    , toPatterns
    , fromPattern
    , fromTermLike
    , fromTermLikeUnsorted
    , bottom
    , isFalse
    , isPredicate
    , top
    , isTrue
    , toPattern
    , toTermLike
    , MultiOr.flatten
    , MultiOr.filterOr
    ) where

import qualified Data.Foldable as Foldable
import qualified GHC.Stack as GHC

import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
    ( fromPredicate
    , toPredicate
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.MultiOr
    ( MultiOr
    )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike hiding
    ( isSimplified
    )
import Kore.TopBottom
    ( TopBottom (..)
    )

{-| The disjunction of 'Pattern'.
-}
type OrPattern variable = MultiOr (Pattern variable)

isSimplified :: OrPattern variable -> Bool
isSimplified = all Pattern.isSimplified

{- | A "disjunction" of one 'Pattern.Pattern'.
 -}
fromPattern
    :: Ord variable
    => Pattern variable
    -> OrPattern variable
fromPattern = MultiOr.singleton

{- | Disjoin a collection of patterns.
 -}
fromPatterns
    :: (Foldable f, Ord variable)
    => f (Pattern variable)
    -> OrPattern variable
fromPatterns = MultiOr.make . Foldable.toList

{- | Examine a disjunction of 'Pattern.Pattern's.
 -}
toPatterns :: OrPattern variable -> [Pattern variable]
toPatterns = MultiOr.extractPatterns

{- | A "disjunction" of one 'TermLike'.

See also: 'fromPattern'

 -}
fromTermLike
    :: InternalVariable variable
    => TermLike variable
    -> OrPattern variable
fromTermLike = fromPattern . Pattern.fromTermLike

fromTermLikeUnsorted
    :: InternalVariable variable
    => TermLike variable
    -> OrPattern variable
fromTermLikeUnsorted = fromPattern . Pattern.fromTermLikeUnsorted

{- | @\\bottom@

@
'isFalse' bottom == True
@

 -}
bottom :: Ord variable => OrPattern variable
bottom = fromPatterns []

{-| 'isFalse' checks if the 'Or' is composed only of bottom items.
-}
isFalse :: OrPattern variable -> Bool
isFalse = isBottom

{- | @\\top@

@
'isTrue' top == True
@

 -}
top :: InternalVariable variable => OrPattern variable
top = fromPattern Pattern.top

{-| 'isTrue' checks if the 'Or' has a single top pattern.
-}
isTrue :: OrPattern variable -> Bool
isTrue = isTop

{-| 'toPattern' transforms an 'OrPattern' into a 'Pattern.Pattern'.
-}
toPattern
    :: forall variable
    .  InternalVariable variable
    => OrPattern variable
    -> Pattern variable
toPattern multiOr =
    case MultiOr.extractPatterns multiOr of
        [] -> Pattern.bottom
        [patt] -> patt
        patts -> Foldable.foldr1 mergeWithOr patts
  where
    mergeWithOr :: Pattern variable -> Pattern variable -> Pattern variable
    mergeWithOr patt1 patt2
      | isTop term1, isTop term2 =
        term1
        `Conditional.withCondition` mergeConditionsWithOr predicate1 predicate2
      | otherwise =
        Pattern.fromTermLike
            (mkOr (Pattern.toTermLike patt1) (Pattern.toTermLike patt2))
      where
        (term1, predicate1) = Pattern.splitTerm patt1
        (term2, predicate2) = Pattern.splitTerm patt2

    mergeConditionsWithOr
        :: Condition variable -> Condition variable -> Condition variable
    mergeConditionsWithOr predicate1 predicate2 =
        Condition.fromPredicate
            (Predicate.makeOrPredicate
                (Condition.toPredicate predicate1)
                (Condition.toPredicate predicate2)
            )

{- Check if an OrPattern can be reduced to a Predicate. -}
isPredicate :: OrPattern variable -> Bool
isPredicate = all Pattern.isPredicate

{-| Transforms a 'Pattern' into a 'TermLike'.
-}
toTermLike
    :: InternalVariable variable
    => OrPattern variable -> TermLike variable
toTermLike multiOr =
    case MultiOr.extractPatterns multiOr of
        [] -> mkBottom_
        [patt] -> Pattern.toTermLike patt
        patts -> Foldable.foldr1 mkOr (Pattern.toTermLike <$> patts)

coerceSort
    :: (GHC.HasCallStack, InternalVariable variable)
    => Sort -> OrPattern variable -> OrPattern variable
coerceSort sort =
    fromPatterns
    . map (Pattern.coerceSort sort)
    . toPatterns

