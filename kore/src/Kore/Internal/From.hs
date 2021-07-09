{- |
Copyright   : (c) Runtime Verification, 2021
License     : BSD-3-Clause
-}
module Kore.Internal.From (
    SynthesizeFrom,
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

{- | Constraint that the pattern type @p@ can be created from syntax type @s@.

* @s :: Type -> Type@ is the syntax type at the top level of the pattern, for
  example: @'And' 'Sort'@ or @'Or' 'Sort'@.
* @a :: Type@ is the type of attribute attached to the syntax tree. We should
  always quantify over @a@; it is only visible here to avoid a quantified
  constraint.
* @v :: Type@ is the type of variable names in the pattern, for example:
  'VariableName' or 'Kore.Rewriting.RewritingVariable.RewritingVariableName'.
  @v@ should not appear by itself, but only as the argument of another type. It
  is visible here to aid type inference.
* @p :: Type -> Type@ is the pattern type, for example: 'Predicate' or
  'TermLike'. @p@ should always appear with @v@, i.e. @p v :: Type@.
* @t :: Type -> Type@ is the term type, for example: 'TermLike'. Some syntax
  types ('Ceil', 'Floor', 'Equals', 'In') can contain a different type of
  pattern than @p@; @t@ represents that type. For all other syntax types, @t@
  will be fixed to @p@.
* @f :: Type -> Type -> Type@ is the base functor describing the shape of @p@;
  that is, @Data.Functor.Foldable.Base (p v) ~ CofreeF (f v) a@.
-}
type SynthesizeFrom
    (s :: Type -> Type)
    (a :: Type)
    (f :: Type -> Type -> Type)
    (v :: Type)
    (t :: Type -> Type)
    (p :: Type -> Type) =
    ( From (s (t v)) (f v (p v))
    , Synthesize a (f v) (p v)
    )

synthesizeFrom ::
    forall s a f v t p. SynthesizeFrom s a f v t p => s (t v) -> p v
synthesizeFrom = synthesize . into @(f v (p v))
{-# INLINE synthesizeFrom #-}

fromAnd ::
    forall a f v p.
    SynthesizeFrom (And ()) a f v p p =>
    p v ->
    p v ->
    p v
fromAnd andFirst andSecond =
    synthesizeFrom And{andFirst, andSecond, andSort = ()}

fromOr :: forall a f v p. SynthesizeFrom (Or ()) a f v p p => p v -> p v -> p v
fromOr orFirst orSecond = synthesizeFrom Or{orFirst, orSecond, orSort = ()}

fromNot :: forall a f v p. SynthesizeFrom (Not ()) a f v p p => p v -> p v
fromNot notChild = synthesizeFrom Not{notChild, notSort = ()}

fromImplies :: forall a f v p. SynthesizeFrom (Implies ()) a f v p p => p v -> p v -> p v
fromImplies impliesFirst impliesSecond =
    synthesizeFrom Implies{impliesFirst, impliesSecond, impliesSort = ()}

fromIff :: forall a f v p. SynthesizeFrom (Iff ()) a f v p p => p v -> p v -> p v
fromIff iffFirst iffSecond =
    synthesizeFrom Iff{iffFirst, iffSecond, iffSort = ()}

fromExists ::
    forall a f v p.
    SynthesizeFrom (Exists () v) a f v p p =>
    ElementVariable v ->
    p v ->
    p v
fromExists existsVariable existsChild =
    synthesizeFrom Exists{existsVariable, existsChild, existsSort = ()}

fromForall ::
    forall a f v p.
    SynthesizeFrom (Forall () v) a f v p p =>
    ElementVariable v ->
    p v ->
    p v
fromForall forallVariable forallChild =
    synthesizeFrom Forall{forallVariable, forallChild, forallSort = ()}

fromBottom_ :: forall a f v p. SynthesizeFrom (Bottom ()) a f v p p => p v
fromBottom_ = synthesizeFrom @_ @a @f @v @p @p Bottom{bottomSort = ()}

fromTop_ :: forall a f v p. SynthesizeFrom (Top ()) a f v p p => p v
fromTop_ = synthesizeFrom @_ @a @f @v @p @p Top{topSort = ()}

fromCeil_ :: forall a f v t p. SynthesizeFrom (Ceil ()) a f v t p => t v -> p v
fromCeil_ ceilChild =
    synthesizeFrom Ceil{ceilChild, ceilOperandSort = (), ceilResultSort = ()}

fromFloor_ ::
    forall a f v t p.
    SynthesizeFrom (Floor ()) a f v t p =>
    t v ->
    p v
fromFloor_ floorChild =
    synthesizeFrom
        Floor
            { floorChild
            , floorOperandSort = ()
            , floorResultSort = ()
            }

fromEquals_ ::
    forall a f v t p.
    SynthesizeFrom (Equals ()) a f v t p =>
    t v ->
    t v ->
    p v
fromEquals_ equalsFirst equalsSecond =
    synthesizeFrom
        Equals
            { equalsFirst
            , equalsSecond
            , equalsOperandSort = ()
            , equalsResultSort = ()
            }

fromIn_ ::
    forall a f v t p.
    SynthesizeFrom (In ()) a f v t p =>
    t v ->
    t v ->
    p v
fromIn_ inContainedChild inContainingChild =
    synthesizeFrom
        In
            { inContainedChild
            , inContainingChild
            , inOperandSort = ()
            , inResultSort = ()
            }
