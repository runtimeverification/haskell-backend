{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}
module Kore.Step.Simplification.InternalSet
    ( simplify
    ) where

import Prelude.Kore

import qualified Control.Lens as Lens
import Data.Generics.Product

import qualified Kore.Builtin.AssociativeCommutative as Builtin
import Kore.Internal.Conditional
    ( Conditional
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.InternalSet
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.Predicate
    ( makeFalsePredicate_
    )
import Kore.Internal.TermLike
import Logic
    ( Logic
    )
import qualified Logic

{-| 'simplify' simplifies a 'DomainValue' pattern, which means returning
an or containing a term made of that value.
-}
simplify
    :: InternalVariable variable
    => InternalSet (TermLike Concrete) (OrPattern variable)
    -> OrPattern variable
simplify internalSet =
    MultiOr.observeAll $ do
        child <- fmap mkBuiltinSet <$> simplifyInternalSet internalSet
        return (markSimplified <$> child)

simplifyInternal
    :: (InternalVariable variable, Traversable t)
    => (t (TermLike variable) -> Maybe (t (TermLike variable)))
    -> t (OrPattern variable)
    -> Logic (Conditional variable (t (TermLike variable)))
simplifyInternal normalizer tOrPattern = do
    conditional <- sequenceA <$> traverse Logic.scatter tOrPattern
    let bottom = conditional `Conditional.andPredicate` makeFalsePredicate_
        normalized = fromMaybe bottom $ traverse normalizer conditional
    return normalized

simplifyInternalSet
    :: InternalVariable variable
    => InternalSet (TermLike Concrete) (OrPattern variable)
    -> Logic (Conditional variable (InternalSet (TermLike Concrete) (TermLike variable)))
simplifyInternalSet = simplifyInternal normalizeInternalSet

normalizeInternalSet
    :: Ord variable
    => InternalSet (TermLike Concrete) (TermLike variable)
    -> Maybe (InternalSet (TermLike Concrete) (TermLike variable))
normalizeInternalSet =
    Lens.traverseOf (field @"builtinAcChild") Builtin.renormalize
