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
    , fromConcretePurePattern
    , asPattern
    , asConcretePurePattern
    ) where

import           Data.Deriving
                 ( deriveEq1, deriveOrd1, deriveShow1 )
import           Data.Functor.Foldable
                 ( Fix (..) )
import qualified Data.Functor.Foldable as Functor.Foldable
import           Data.Reflection
                 ( give )

import           Kore.AST.Common
                 ( Concrete, ConcretePurePattern, Pattern (..) )
import qualified Kore.AST.Common as Pattern
import           Kore.AST.MetaOrObject
import           Kore.IndexedModule.MetadataTools
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
        :: !(Pattern.DomainValue Object (Pattern.BuiltinDomain child))
        -> ValueF Object child

deriving instance Eq child => Eq (ValueF level child)
deriving instance Ord child => Ord (ValueF level child)
deriving instance Show child => Show (ValueF level child)

deriving instance Functor (ValueF level)
deriving instance Foldable (ValueF level)
deriving instance Traversable (ValueF level)

deriveEq1 ''ValueF
deriveOrd1 ''ValueF
deriveShow1 ''ValueF

type Value level = Fix (ValueF level)

{- | Project a sort injection head to @Nothing@.

    Used in 'fromPattern' to ensure that the children of a sort injection are
    not sort injections, i.e. that the triangle axiom for sort injections has
    been fully applied.
 -}
eraseSortInjection :: Value level -> Maybe (Value level)
eraseSortInjection val =
    case Functor.Foldable.project val of
        Constructor _ -> Just val
        DomainValue _ -> Just val
        SortInjection _ -> Nothing

{- | Embed the normalized pattern head if its children are normal values.

    See also: 'fromConcretePurePattern'.

 -}
fromPattern
    :: MetadataTools level StepperAttributes
    -> Pattern level Concrete (Maybe (Value level))
    -> Maybe (Value level)
fromPattern tools =
    \case
        ApplicationPattern
            appP@Pattern.Application
                { applicationSymbolOrAlias = symbolOrAlias }
          | isConstructor symbolOrAlias ->
            -- The constructor application is normal if all its children are
            -- normal.
            Fix . Constructor <$> sequence appP
          | isSortInjection symbolOrAlias ->
            -- The sort injection application is normal if all its children are
            -- normal and none are sort injections.
            Fix . SortInjection <$> traverse (>>= eraseSortInjection) appP
        DomainValuePattern dvP ->
            -- A domain value is not technically a constructor, but it is
            -- constructor-like for builtin domains, at least from the
            -- perspective of normalization.
            -- TODO (thomas.tuegel): Builtin domain parsers may violate the
            -- assumption that domain values are concrete. We should remove
            -- BuiltinDomainPattern and always run the stepper with internal
            -- representations only.
            Fix . DomainValue <$> traverse sequence dvP
        _ -> Nothing
  where
    isConstructor = give tools isConstructor_
    isSortInjection = give tools isSortInjection_

{- | View a 'ConcretePurePattern' as a normalized value.

    The pattern is considered normalized if it is a domain value, a constructor,
    or a sort injection applied only to normalized value.

    See also: 'fromPattern'

 -}
fromConcretePurePattern
    :: MetadataTools level StepperAttributes
    -> ConcretePurePattern level
    -> Maybe (Value level)
fromConcretePurePattern tools =
    Functor.Foldable.fold (fromPattern tools)

{- | Project a 'Value' to a concrete 'Pattern' head.
 -}
asPattern :: Value level -> Pattern level Concrete (Value level)
asPattern val =
    case Functor.Foldable.project val of
        Constructor appP -> ApplicationPattern appP
        SortInjection appP -> ApplicationPattern appP
        DomainValue dvP -> DomainValuePattern dvP

{- | View a normalized value as a 'ConcretePurePattern'.
 -}
asConcretePurePattern :: Value level -> ConcretePurePattern level
asConcretePurePattern = Functor.Foldable.unfold asPattern
