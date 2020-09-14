{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Internal.OrPattern
    ( OrPattern
    , coerceSort
    , isSimplified
    , forgetSimplified
    , fromPatterns
    , toPatterns
    , fromPattern
    , fromTermLike
    , bottom
    , isFalse
    , isPredicate
    , top
    , isTrue
    , toPattern
    , toTermLike
    , targetBinder
    , substitute
    , MultiOr.flatten
    , MultiOr.filterOr
    , MultiOr.gather
    , MultiOr.observeAllT
    , MultiOr.map
    , MultiOr.traverse
    , MultiOr.traverseLogic
    ) where

import Prelude.Kore

import qualified Data.Foldable as Foldable
import Data.Map.Strict
    ( Map
    )
import Data.MonoTraversable
    ( Element
    , MonoFoldable (..)
    , MonoFunctor (..)
    )
import qualified GHC.Generics as GHC

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
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
    ( Representation
    )
import Kore.Internal.TermLike
    ( InternalVariable
    , Sort
    , TermLike
    , mkBottom_
    , mkOr
    )
import Kore.Syntax.Variable
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Variables.Binding
    ( Binder (..)
    )
import Kore.Variables.Target
    ( Target (..)
    , mkElementTarget
    , targetIfEqual
    )

{-| The disjunction of 'Pattern's.
-}
newtype OrPattern variable =
    OrPattern { unOrPattern :: MultiOr (Pattern variable) }
    deriving
        ( Eq
        , Ord
        , Show
        , GHC.Generic
        , Semigroup
        , Monoid
        )

type instance Element (OrPattern variable) = Pattern variable

instance MonoFoldable (OrPattern variable) where
    ofoldMap f (OrPattern multiOr) = foldMap f multiOr
    ofoldr f def (OrPattern multiOr) = foldr f def multiOr
    ofoldl' f def (OrPattern multiOr) = foldl f def multiOr
    ofoldr1Ex f (OrPattern multiOr) = foldr1 f multiOr
    ofoldl1Ex' f (OrPattern multiOr) = foldl1 f multiOr

instance MonoFunctor (OrPattern variable) where
    omap f (OrPattern multiOr) = OrPattern (MultiOr.map f multiOr)

isSimplified :: SideCondition.Representation -> OrPattern variable -> Bool
isSimplified sideCondition = oall (Pattern.isSimplified sideCondition)

forgetSimplified
    :: InternalVariable variable => OrPattern variable -> OrPattern variable
forgetSimplified = fromPatterns . map Pattern.forgetSimplified . toPatterns

{- | A "disjunction" of one 'Pattern.Pattern'.
 -}
fromPattern :: Pattern variable -> OrPattern variable
fromPattern = from

{- | Disjoin a collection of patterns.
 -}
fromPatterns
    :: (Foldable f, InternalVariable variable)
    => f (Pattern variable)
    -> OrPattern variable
fromPatterns = from . Foldable.toList

{- | Examine a disjunction of 'Pattern.Pattern's.
 -}
toPatterns :: OrPattern variable -> [Pattern variable]
toPatterns = from

{- | A "disjunction" of one 'TermLike'.

See also: 'fromPattern'

 -}
fromTermLike
    :: InternalVariable variable
    => TermLike variable
    -> OrPattern variable
fromTermLike = fromPattern . Pattern.fromTermLike

{- | @\\bottom@

@
'isFalse' bottom == True
@

 -}
bottom :: InternalVariable variable => OrPattern variable
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
toPattern (OrPattern multiOr) =
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
isPredicate = oall Pattern.isPredicate

{-| Transforms a 'Pattern' into a 'TermLike'.
-}
toTermLike
    :: InternalVariable variable
    => OrPattern variable -> TermLike variable
toTermLike (OrPattern multiOr) =
    case MultiOr.extractPatterns multiOr of
        [] -> mkBottom_
        [patt] -> Pattern.toTermLike patt
        patts -> Foldable.foldr1 mkOr (Pattern.toTermLike <$> patts)

coerceSort
    :: (HasCallStack, InternalVariable variable)
    => Sort -> OrPattern variable -> OrPattern variable
coerceSort sort =
    fromPatterns
    . map (Pattern.coerceSort sort)
    . toPatterns

targetBinder
    :: forall variable
    .  InternalVariable variable
    => Binder (ElementVariable variable) (OrPattern variable)
    -> Binder (ElementVariable (Target variable)) (OrPattern (Target variable))
targetBinder Binder { binderVariable, binderChild } =
    let newVar = mkElementTarget binderVariable
        targetBoundVariables =
            targetIfEqual
            $ unElementVariableName . variableName $ binderVariable
        newChild :: OrPattern (Target variable)
        newChild =
            omap
                (Pattern.mapVariables
                    AdjSomeVariableName
                    { adjSomeVariableNameElement =
                        ElementVariableName targetBoundVariables
                    , adjSomeVariableNameSet = SetVariableName NonTarget
                    }
                )
                binderChild
     in Binder
         { binderVariable = newVar
         , binderChild = undefined
         }

substitute
    :: InternalVariable variable
    => Map (SomeVariableName variable) (TermLike variable)
    -> OrPattern variable
    -> OrPattern variable
substitute subst =
    fromPatterns . fmap (Pattern.substitute subst) . toPatterns
