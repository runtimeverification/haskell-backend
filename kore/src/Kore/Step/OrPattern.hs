{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.OrPattern
    ( OrPattern
    , fromPatterns
    , fromPattern
    , fromTermLike
    , bottom
    , isFalse
    , top
    , isTrue
    , toExpandedPattern
    , toTermLike
    ) where

import qualified Data.Foldable as Foldable

import           Kore.AST.MetaOrObject
import           Kore.AST.Valid
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import qualified Kore.Step.Conditional as Conditional
import           Kore.Step.Pattern
                 ( Pattern )
import qualified Kore.Step.Pattern as Pattern
import           Kore.Step.Representation.MultiOr
                 ( MultiOr )
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.Step.TermLike
import           Kore.TopBottom
                 ( TopBottom (..) )
import           Kore.Unparser

{-| The disjunction of 'Pattern'.
-}
type OrPattern level variable = MultiOr (Pattern level variable)

{- | A "disjunction" of one 'Pattern.Pattern'.
 -}
fromPattern
    :: Ord (variable Object)
    => Pattern Object variable
    -> OrPattern Object variable
fromPattern = MultiOr.singleton

{- | Disjoin a collection of patterns.
 -}
fromPatterns
    :: (Foldable f, Ord (variable Object))
    => f (Pattern Object variable)
    -> OrPattern Object variable
fromPatterns = MultiOr.make . Foldable.toList

{- | A "disjunction" of one 'TermLike'.

See also: 'fromPattern'

 -}
fromTermLike
    :: Ord (variable Object)
    => TermLike variable
    -> OrPattern Object variable
fromTermLike = fromPattern . Pattern.fromTermLike

{- | @\\bottom@

@
'isFalse' bottom == True
@

 -}
bottom :: Ord (variable Object) => OrPattern Object variable
bottom = fromPatterns []

{-| 'isFalse' checks if the 'Or' is composed only of bottom items.
-}
isFalse :: Ord (variable Object) => OrPattern Object variable -> Bool
isFalse = isBottom

{- | @\\top@

@
'isTrue' top == True
@

 -}
top :: Ord (variable Object) => OrPattern Object variable
top = fromPattern Pattern.top

{-| 'isTrue' checks if the 'Or' has a single top pattern.
-}
isTrue :: Ord (variable Object) => OrPattern Object variable -> Bool
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
    => OrPattern Object variable -> Pattern Object variable
toExpandedPattern multiOr
  =
    case MultiOr.extractPatterns multiOr of
        [] -> Pattern.bottom
        [patt] -> patt
        patts ->
            Conditional.Conditional
                { term = Foldable.foldr1 mkOr (Pattern.toMLPattern <$> patts)
                , predicate = Syntax.Predicate.makeTruePredicate
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
    => OrPattern Object variable -> TermLike variable
toTermLike multiOr =
    case MultiOr.extractPatterns multiOr of
        [] -> mkBottom_
        [patt] -> Pattern.toMLPattern patt
        patts -> Foldable.foldr1 mkOr (Pattern.toMLPattern <$> patts)
