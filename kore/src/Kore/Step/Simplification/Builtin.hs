{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}
module Kore.Step.Simplification.Builtin
    ( simplify
    ) where

import qualified Control.Lens as Lens
import Data.Functor.Compose
import Data.Generics.Product
import Data.Maybe

import qualified Kore.Builtin.AssociativeCommutative as Builtin
import Kore.Domain.Builtin
    ( InternalMap
    , InternalSet
    )
import qualified Kore.Domain.Builtin as Domain
import Kore.Internal.Conditional
    ( Conditional
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.TermLike
import Kore.Predicate.Predicate
    ( makeFalsePredicate
    )

{-| 'simplify' simplifies a 'DomainValue' pattern, which means returning
an or containing a term made of that value.
-}
simplify
    :: InternalVariable variable
    => Builtin (OrPattern variable)
    -> OrPattern variable
simplify builtin =
    MultiOr.filterOr $ do
        child <- simplifyBuiltin builtin
        return (markSimplified . mkBuiltin <$> child)

simplifyBuiltin
    :: InternalVariable variable
    => Builtin (OrPattern variable)
    -> MultiOr (Conditional variable (Builtin (TermLike variable)))
simplifyBuiltin =
    \case
        Domain.BuiltinMap map' -> simplifyInternalMap map'
        Domain.BuiltinList list' -> simplifyInternalList list'
        Domain.BuiltinSet set' -> simplifyInternalSet set'
        Domain.BuiltinInt int -> (return . pure) (Domain.BuiltinInt int)
        Domain.BuiltinBool bool -> (return . pure) (Domain.BuiltinBool bool)
        Domain.BuiltinString string ->
            (return . pure) (Domain.BuiltinString string)

simplifyInternal
    :: (InternalVariable variable, Traversable t)
    => (t (TermLike variable) -> Maybe (t (TermLike variable)))
    -> t (OrPattern variable)
    -> MultiOr (Conditional variable (t (TermLike variable)))
simplifyInternal normalizer tOrPattern = do
    conditional <- getCompose $ traverse Compose tOrPattern
    let bottom = conditional `Conditional.andPredicate` makeFalsePredicate
        normalized = fromMaybe bottom $ traverse normalizer conditional
    return normalized

simplifyInternalMap
    :: InternalVariable variable
    => Domain.InternalMap (TermLike Concrete) (OrPattern variable)
    -> MultiOr (Conditional variable (Builtin (TermLike variable)))
simplifyInternalMap =
    (fmap . fmap) Domain.BuiltinMap
    . simplifyInternal normalizeInternalMap

normalizeInternalMap
    :: Ord variable
    => InternalMap (TermLike Concrete) (TermLike variable)
    -> Maybe (InternalMap (TermLike Concrete) (TermLike variable))
normalizeInternalMap =
    Lens.traverseOf (field @"builtinAcChild") Builtin.renormalize

simplifyInternalSet
    :: InternalVariable variable
    => Domain.InternalSet (TermLike Concrete) (OrPattern variable)
    -> MultiOr (Conditional variable (Builtin (TermLike variable)))
simplifyInternalSet =
    (fmap . fmap) Domain.BuiltinSet
    . simplifyInternal normalizeInternalSet

normalizeInternalSet
    :: Ord variable
    => InternalSet (TermLike Concrete) (TermLike variable)
    -> Maybe (InternalSet (TermLike Concrete) (TermLike variable))
normalizeInternalSet =
    Lens.traverseOf (field @"builtinAcChild") Builtin.renormalize

simplifyInternalList
    :: InternalVariable variable
    => Domain.InternalList (OrPattern variable)
    -> MultiOr (Conditional variable (Builtin (TermLike variable)))
simplifyInternalList = (fmap . fmap) Domain.BuiltinList . simplifyInternal pure
