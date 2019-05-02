{- |
Module      : Kore.Proof.Value
Description : Proof that a pattern is a fully-evaluated term
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
 -}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Proof.Value
    ( ValueF (..)
    , Value
    , fromPattern
    , Kore.Proof.Value.fromConcreteStepPattern
    , asPattern
    , Kore.Proof.Value.asConcreteStepPattern
    ) where

import           Control.Comonad.Trans.Cofree
                 ( Cofree )
import qualified Control.Comonad.Trans.Cofree as Cofree
import qualified Data.Deriving as Deriving
import           Data.Functor.Compose
import           Data.Functor.Foldable
                 ( Base, Corecursive, Recursive )
import qualified Data.Functor.Foldable as Recursive
import           Data.Functor.Identity
import           Data.Reflection
                 ( give )
import           GHC.Generics
                 ( Generic )

import qualified Kore.Attribute.Pattern as Attribute
                 ( Pattern (..) )
import           Kore.Attribute.Symbol
                 ( StepperAttributes, isConstructor_, isSortInjection_ )
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
import           Kore.Internal.TermLike
                 ( Concrete, TermLike )
import qualified Kore.Syntax as Syntax
import           Kore.Syntax.Application
import           Kore.Syntax.Pattern
                 ( CofreeF (..), PatternF (..) )

{- | Proof (by construction) that a pattern is a normalized value.

    A normal pattern head is either a constructor (or a constructor-like domain
    value), a sort injection, or a domain value.
 -}
data ValueF child
    = Constructor !(Application SymbolOrAlias child)
    | SortInjection !(Application SymbolOrAlias child)
    | DomainValue !(Domain.Builtin child)
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

Deriving.deriveEq1 ''ValueF
Deriving.deriveOrd1 ''ValueF
Deriving.deriveShow1 ''ValueF

newtype Value =
    Value { getValue :: Cofree ValueF (Attribute.Pattern Concrete) }
    deriving (Eq, Generic, Ord, Show)

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
eraseSortInjection (Recursive.project -> ann :< value) =
    case value of
        Constructor _ -> (Just . Recursive.embed) (ann :< value)
        DomainValue _ -> (Just . Recursive.embed) (ann :< value)
        SortInjection _ -> Nothing

{- | Embed the normalized pattern head if its children are normal values.

    See also: 'fromConcretePurePattern'.

 -}
fromPattern
    :: SmtMetadataTools StepperAttributes
    -> Base (TermLike Concrete) (Maybe Value)
    -> Maybe Value
fromPattern tools (ann :< pat) =
    case pat of
        ApplicationF
            appP@Syntax.Application
                { applicationSymbolOrAlias = symbolOrAlias }
          | isConstructor symbolOrAlias ->
            -- The constructor application is normal if all its children are
            -- normal.
            Recursive.embed . (ann :<) . Constructor <$> sequence appP
          | isSortInjection symbolOrAlias ->
            -- The sort injection application is normal if all its children are
            -- normal and none are sort injections.
            Recursive.embed . (ann :<) . SortInjection
                <$> traverse (>>= eraseSortInjection) appP
        DomainValueF dvP ->
            -- A domain value is not technically a constructor, but it is
            -- constructor-like for builtin domains, at least from the
            -- perspective of normalization.
            -- TODO (thomas.tuegel): Builtin domain parsers may violate the
            -- assumption that domain values are concrete. We should remove
            -- BuiltinPattern and always run the stepper with internal
            -- representations only.
            Recursive.embed . (ann :<) . DomainValue <$> sequence dvP
        _ -> Nothing
  where
    isConstructor = give tools isConstructor_
    isSortInjection = give tools isSortInjection_

{- | View a 'ConcreteStepPattern' as a normalized value.

The pattern is considered normalized if it is a domain value, a constructor, or
a sort injection applied only to normalized value.

See also: 'fromPattern'

 -}
fromConcreteStepPattern
    :: SmtMetadataTools StepperAttributes
    -> TermLike Concrete
    -> Maybe Value
fromConcreteStepPattern tools =
    Recursive.fold (fromPattern tools)

{- | Project a 'Value' to a concrete 'Pattern' head.
 -}
asPattern :: Value -> Base (TermLike Concrete) Value
asPattern (Recursive.project -> ann :< val) =
    case val of
        Constructor appP -> ann :< ApplicationF appP
        SortInjection appP -> ann :< ApplicationF appP
        DomainValue dvP -> ann :< DomainValueF dvP

{- | View a normalized value as a 'ConcreteStepPattern'.
 -}
asConcreteStepPattern :: Value -> TermLike Concrete
asConcreteStepPattern = Recursive.unfold asPattern
