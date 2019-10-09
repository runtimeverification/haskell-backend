{- |
Module      : Kore.Proof.Value
Description : Proof that a pattern is a fully-evaluated term
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
 -}

module Kore.Proof.Value
    ( ValueF (..)
    , Value
    , fromPattern
    , fromTermLike
    , asPattern
    , asTermLike
    ) where

import Control.Comonad.Trans.Cofree
    ( Cofree
    , CofreeF (..)
    )
import qualified Control.Comonad.Trans.Cofree as Cofree
import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Foldable
    ( Base
    , Corecursive
    , Recursive
    )
import qualified Data.Functor.Foldable as Recursive
import Data.Functor.Identity
import GHC.Generics
    ( Generic
    )

import qualified Kore.Attribute.Pattern as Attribute
    ( Pattern (..)
    )
import qualified Kore.Domain.Builtin as Domain
import Kore.Internal.Symbol
import Kore.Internal.TermLike
    ( TermLike
    , TermLikeF (..)
    )
import Kore.Sort
import qualified Kore.Syntax.Application as Syntax
import qualified Kore.Syntax.DomainValue as Syntax
import Kore.Syntax.StringLiteral
    ( StringLiteral
    )
import Kore.Syntax.Variable

{- | Proof (by construction) that a pattern is a normalized value.

    A normal pattern head is either a constructor (or a constructor-like domain
    value), a sort injection, or a domain value.
 -}
data ValueF child
    = Constructor !(Syntax.Application Symbol child)
    | SortInjection !(Syntax.Application Symbol child)
    | DomainValue !(Syntax.DomainValue Sort child)
    | Builtin !(Domain.Builtin (TermLike Concrete) child)
    | StringLiteral !StringLiteral
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

newtype Value =
    Value { getValue :: Cofree ValueF (Attribute.Pattern Concrete) }
    deriving (Eq, Generic, Show)

type instance Base Value = CofreeF ValueF (Attribute.Pattern Concrete)

instance Recursive Value where
    project (Value embedded) =
        case Recursive.project embedded of
            Compose (Identity projected) -> Value <$> projected

instance Corecursive Value where
    embed projected =
        (Value . Recursive.embed . Compose . Identity)
            (getValue <$> projected)

{- | Project a sort injection head to @Nothing@.

Used in 'fromPattern' to ensure that the children of a sort injection are
not sort injections, i.e. that the triangle axiom for sort injections has
been fully applied.

 -}
eraseSortInjection :: Value -> Maybe Value
eraseSortInjection original@(Recursive.project -> _ :< value) =
    case value of
        SortInjection _ -> Nothing
        _               -> Just original

{- | Embed the normalized pattern head if its children are normal values.

    See also: 'fromConcretePattern'.

 -}
fromPattern
    :: Base (TermLike Concrete) (Maybe Value)
    -> Maybe Value
fromPattern (attrs :< termLikeF) =
    fmap (Recursive.embed . (attrs :<))
    $ case termLikeF of
        ApplySymbolF applySymbolF
          | isConstructor symbol ->
            -- The constructor application is normal if all its children are
            -- normal.
            Constructor <$> sequence applySymbolF
          | isSortInjection symbol ->
            -- The sort injection application is normal if all its children are
            -- normal and none are sort injections.
            SortInjection <$> traverse (>>= eraseSortInjection) applySymbolF
          where
            symbol = Syntax.applicationSymbolOrAlias applySymbolF
        DomainValueF dvP ->
            -- A domain value is not technically a constructor, but it is
            -- constructor-like for builtin domains, at least from the
            -- perspective of normalization.
            -- TODO (thomas.tuegel): Builtin domain parsers may violate the
            -- assumption that domain values are concrete. We should remove
            -- BuiltinPattern and always run the stepper with internal
            -- representations only.
            DomainValue <$> sequence dvP
        BuiltinF builtinP ->
            -- A domain value is not technically a constructor, but it is
            -- constructor-like for builtin domains, at least from the
            -- perspective of normalization.
            -- TODO (thomas.tuegel): Builtin domain parsers may violate the
            -- assumption that domain values are concrete. We should remove
            -- BuiltinPattern and always run the stepper with internal
            -- representations only.
            Builtin <$> sequence builtinP
        StringLiteralF (Const stringL) -> pure (StringLiteral stringL)
        _ -> Nothing

{- | View a 'ConcreteStepPattern' as a normalized value.

The pattern is considered normalized if it is a domain value, a constructor, or
a sort injection applied only to normalized value.

See also: 'fromPattern'

 -}
fromTermLike :: TermLike Concrete -> Maybe Value
fromTermLike = Recursive.fold fromPattern

{- | Project a 'Value' to a concrete 'Pattern' head.
 -}
asPattern :: Value -> Base (TermLike Concrete) Value
asPattern (Recursive.project -> attrs :< value) =
    case value of
        Constructor appP      -> attrs :< ApplySymbolF   appP
        SortInjection appP    -> attrs :< ApplySymbolF   appP
        DomainValue dvP       -> attrs :< DomainValueF   dvP
        Builtin builtinP      -> attrs :< BuiltinF       builtinP
        StringLiteral stringP -> attrs :< StringLiteralF (Const stringP)

{- | View a normalized value as a 'ConcreteStepPattern'.
 -}
asTermLike :: Value -> TermLike Concrete
asTermLike = Recursive.unfold asPattern
