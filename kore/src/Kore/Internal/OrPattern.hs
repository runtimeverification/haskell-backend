{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Internal.OrPattern
    ( OrPattern
    , fromPatterns
    , fromPattern
    , fromTermLike
    , bottom
    , isFalse
    , top
    , isTrue
    , toPattern
    , toTermLike
    , MultiOr.flatten
    ) where

import qualified Data.Foldable as Foldable

import qualified Kore.Internal.Conditional as Conditional
import           Kore.Internal.MultiOr
                 ( MultiOr )
import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.Pattern
                 ( Pattern )
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import           Kore.TopBottom
                 ( TopBottom (..) )
import           Kore.Unparser

{-| The disjunction of 'Pattern'.
-}
type OrPattern variable = MultiOr (Pattern variable)

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

{- | A "disjunction" of one 'TermLike'.

See also: 'fromPattern'

 -}
fromTermLike
    :: Ord variable
    => TermLike variable
    -> OrPattern variable
fromTermLike = fromPattern . Pattern.fromTermLike

{- | @\\bottom@

@
'isFalse' bottom == True
@

 -}
bottom :: Ord variable => OrPattern variable
bottom = fromPatterns []

{-| 'isFalse' checks if the 'Or' is composed only of bottom items.
-}
isFalse :: Ord variable => OrPattern variable -> Bool
isFalse = isBottom

{- | @\\top@

@
'isTrue' top == True
@

 -}
top :: Ord variable => OrPattern variable
top = fromPattern Pattern.top

{-| 'isTrue' checks if the 'Or' has a single top pattern.
-}
isTrue :: Ord variable => OrPattern variable -> Bool
isTrue = isTop

{-| 'toPattern' transforms an 'Pattern' into
an 'Pattern.Pattern'.
-}
toPattern
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => OrPattern variable -> Pattern variable
toPattern multiOr =
    case MultiOr.extractPatterns multiOr of
        [] -> Pattern.bottom
        [patt] -> patt
        patts ->
            Conditional.Conditional
                { term = Foldable.foldr1 mkOr (Pattern.toTermLike <$> patts)
                , predicate = Syntax.Predicate.makeTruePredicate
                , substitution = mempty
                }

{-| Transforms a 'Pattern' into a 'TermLike'.
-}
toTermLike
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => OrPattern variable -> TermLike variable
toTermLike multiOr =
    case MultiOr.extractPatterns multiOr of
        [] -> mkBottom_
        [patt] -> Pattern.toTermLike patt
        patts -> Foldable.foldr1 mkOr (Pattern.toTermLike <$> patts)
