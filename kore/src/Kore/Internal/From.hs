module Kore.Internal.From (
    fromAnd,
    fromOr,
    fromNot,
    fromImplies,
    fromIff,
    fromExists,
    fromForall,
    fromBottom_,
    fromTop_,
    fromCeil_,
    fromFloor_,
    fromEquals_,
    fromIn_,
) where

import Data.Kind (Type)
import Kore.Attribute.Synthetic (
    Synthesize,
    synthesize,
 )
import Kore.Syntax.And
import Kore.Syntax.Bottom
import Kore.Syntax.Ceil
import Kore.Syntax.Equals
import Kore.Syntax.Exists
import Kore.Syntax.Floor
import Kore.Syntax.Forall
import Kore.Syntax.Iff
import Kore.Syntax.Implies
import Kore.Syntax.In
import Kore.Syntax.Not
import Kore.Syntax.Or
import Kore.Syntax.Top
import Kore.Syntax.Variable
import Prelude.Kore

type SynthesizeFrom
    (syntax :: Type)
    (a :: Type)
    (f :: Type -> Type)
    (p :: Type) =
    ( From syntax (f p)
    , Synthesize a f p
    )

synthesizeFrom ::
    forall syntax a f p. SynthesizeFrom syntax a f p => syntax -> p
synthesizeFrom = synthesize . into @(f p)
{-# INLINE synthesizeFrom #-}

fromAnd :: forall a f p. SynthesizeFrom (And () p) a f p => p -> p -> p
fromAnd andFirst andSecond =
    synthesizeFrom And{andFirst, andSecond, andSort = ()}

fromOr :: forall a f p. SynthesizeFrom (Or () p) a f p => p -> p -> p
fromOr orFirst orSecond = synthesizeFrom Or{orFirst, orSecond, orSort = ()}

fromNot :: forall a f p. SynthesizeFrom (Not () p) a f p => p -> p
fromNot notChild = synthesizeFrom Not{notChild, notSort = ()}

fromImplies :: forall a f p. SynthesizeFrom (Implies () p) a f p => p -> p -> p
fromImplies impliesFirst impliesSecond =
    synthesizeFrom Implies{impliesFirst, impliesSecond, impliesSort = ()}

fromIff :: forall a f p. SynthesizeFrom (Iff () p) a f p => p -> p -> p
fromIff iffFirst iffSecond =
    synthesizeFrom Iff{iffFirst, iffSecond, iffSort = ()}

fromExists ::
    forall a f p v.
    SynthesizeFrom (Exists () v p) a f p =>
    ElementVariable v ->
    p ->
    p
fromExists existsVariable existsChild =
    synthesizeFrom Exists{existsVariable, existsChild, existsSort = ()}

fromForall ::
    forall a f p v.
    SynthesizeFrom (Forall () v p) a f p =>
    ElementVariable v ->
    p ->
    p
fromForall forallVariable forallChild =
    synthesizeFrom Forall{forallVariable, forallChild, forallSort = ()}

fromBottom_ :: forall a f p. SynthesizeFrom (Bottom () p) a f p => p
fromBottom_ = synthesizeFrom @(Bottom _ p) Bottom{bottomSort = ()}

fromTop_ :: forall a f p. SynthesizeFrom (Top () p) a f p => p
fromTop_ = synthesizeFrom @(Top _ p) Top{topSort = ()}

fromCeil_ :: forall a f t p. SynthesizeFrom (Ceil () t) a f p => t -> p
fromCeil_ ceilChild =
    synthesizeFrom Ceil{ceilChild, ceilOperandSort = (), ceilResultSort = ()}

fromFloor_ :: forall a f t p. SynthesizeFrom (Floor () t) a f p => t -> p
fromFloor_ floorChild =
    synthesizeFrom
        Floor
            { floorChild
            , floorOperandSort = ()
            , floorResultSort = ()
            }

fromEquals_ :: forall a f t p. SynthesizeFrom (Equals () t) a f p => t -> t -> p
fromEquals_ equalsFirst equalsSecond =
    synthesizeFrom
        Equals
            { equalsFirst
            , equalsSecond
            , equalsOperandSort = ()
            , equalsResultSort = ()
            }

fromIn_ :: forall a f t p. SynthesizeFrom (In () t) a f p => t -> t -> p
fromIn_ inContainedChild inContainingChild =
    synthesizeFrom
        In
            { inContainedChild
            , inContainingChild
            , inOperandSort = ()
            , inResultSort = ()
            }
