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
import           Data.Functor.Classes
import           Data.Functor.Compose
import           Data.Functor.Foldable
                 ( Base, Corecursive, Recursive )
import qualified Data.Functor.Foldable as Recursive
import           Data.Functor.Identity
import           Data.Reflection
                 ( give )
import           GHC.Generics
                 ( Generic )

import           Kore.Annotation.Valid
import           Kore.AST.Pure
                 ( CofreeF (..), Object, Pattern (..) )
import qualified Kore.AST.Pure as Pattern
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
import           Kore.Step.Pattern
import           Kore.Step.StepperAttributes
                 ( StepperAttributes, isConstructor_, isSortInjection_ )

{- | Proof (by construction) that a pattern is a normalized value.

    A normal pattern head is either a constructor (or a constructor-like domain
    value), a sort injection, or a domain value.
 -}
data ValueF level child where
    Constructor :: !(Pattern.Application level child) -> ValueF level child
    SortInjection :: !(Pattern.Application level child) -> ValueF level child
    DomainValue
        :: !(Pattern.DomainValue Object Domain.Builtin child)
        -> ValueF Object child

deriving instance Eq child => Eq (ValueF level child)
deriving instance Ord child => Ord (ValueF level child)
deriving instance Show child => Show (ValueF level child)

deriving instance Functor (ValueF level)
deriving instance Foldable (ValueF level)
deriving instance Traversable (ValueF level)

$(return [])

instance Eq1 (ValueF level) where
    liftEq = $(Deriving.makeLiftEq ''ValueF)

instance Ord1 (ValueF level) where
    liftCompare = $(Deriving.makeLiftCompare ''ValueF)

instance Show1 (ValueF level) where
    liftShowsPrec = $(Deriving.makeLiftShowsPrec ''ValueF)

newtype Value (level :: *) =
    Value { getValue :: Cofree (ValueF level) (Valid (Concrete level) level) }
    deriving (Eq, Generic, Ord, Show)

type instance Base (Value level) =
    CofreeF (ValueF level) (Valid (Concrete level) level)

instance Recursive (Value level) where
    project (Value embedded) =
        case Recursive.project embedded of
            Compose (Identity projected) -> Value <$> projected

instance Corecursive (Value level) where
    embed projected =
        (Value . Recursive.embed . Compose . Identity)
            (getValue <$> projected)

{- | Project a sort injection head to @Nothing@.

    Used in 'fromPattern' to ensure that the children of a sort injection are
    not sort injections, i.e. that the triangle axiom for sort injections has
    been fully applied.
 -}
eraseSortInjection :: Value level -> Maybe (Value level)
eraseSortInjection (Recursive.project -> ann :< value) =
    case value of
        Constructor _ -> (Just . Recursive.embed) (ann :< value)
        DomainValue _ -> (Just . Recursive.embed) (ann :< value)
        SortInjection _ -> Nothing

{- | Embed the normalized pattern head if its children are normal values.

    See also: 'fromConcretePurePattern'.

 -}
fromPattern
    :: MetadataTools level StepperAttributes
    -> Base (ConcreteStepPattern level) (Maybe (Value level))
    -> Maybe (Value level)
fromPattern tools (ann :< pat) =
    case pat of
        ApplicationPattern
            appP@Pattern.Application
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
        DomainValuePattern dvP ->
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
    :: MetadataTools level StepperAttributes
    -> ConcreteStepPattern level
    -> Maybe (Value level)
fromConcreteStepPattern tools =
    Recursive.fold (fromPattern tools)

{- | Project a 'Value' to a concrete 'Pattern' head.
 -}
asPattern :: Value level -> Base (ConcreteStepPattern level) (Value level)
asPattern (Recursive.project -> ann :< val) =
    case val of
        Constructor appP -> ann :< ApplicationPattern appP
        SortInjection appP -> ann :< ApplicationPattern appP
        DomainValue dvP -> ann :< DomainValuePattern dvP

{- | View a normalized value as a 'ConcreteStepPattern'.
 -}
asConcreteStepPattern :: Value level -> ConcreteStepPattern level
asConcreteStepPattern = Recursive.unfold asPattern
