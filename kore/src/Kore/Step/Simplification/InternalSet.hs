{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}
module Kore.Step.Simplification.InternalSet
    ( simplify
    ) where

import Prelude.Kore

import qualified Control.Lens as Lens
import Data.Functor.Compose
import Data.Generics.Product

import qualified Kore.Builtin.AssociativeCommutative as Builtin
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.InternalSet
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
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
simplify =
    simplifyInternal
    >>> fmap Pattern.syncSort
    >>> (fmap . fmap) (markSimplified)
    >>> MultiOr.observeAll

simplifyInternal
    :: InternalVariable variable
    => InternalSet (TermLike Concrete) (OrPattern variable)
    -> Logic (Pattern variable)
simplifyInternal internalSet = do
    conditional <- getCompose $ traverse (Logic.scatter >>> Compose) internalSet
    let bottom = conditional `Conditional.andPredicate` makeFalsePredicate_
        normalized = fromMaybe bottom $ traverse normalizeInternalSet conditional
    return (mkBuiltinSet <$> normalized)

normalizeInternalSet
    :: Ord variable
    => InternalSet (TermLike Concrete) (TermLike variable)
    -> Maybe (InternalSet (TermLike Concrete) (TermLike variable))
normalizeInternalSet =
    Lens.traverseOf (field @"builtinAcChild") Builtin.renormalize
