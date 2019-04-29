{-|
Module      : Kore.Proof.Functional
Description : Proofs of functionality and totality of patterns
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}

module Kore.Proof.Functional
    ( ConstructorLikeProof (..)
    , FunctionProof (..)
    , FunctionalProof (..)
    , TotalProof (..)
    , mapVariables
    ) where

import Data.Hashable
       ( Hashable )
import GHC.Generics
       ( Generic )

import           Kore.AST.Common
                 ( CharLiteral, StringLiteral, SymbolOrAlias )
import           Kore.AST.MetaOrObject
                 ( Object )
import qualified Kore.Domain.Builtin as Domain

-- |'FunctionalProof' is used for providing arguments that a pattern is
-- functional.  Currently we only support arguments stating that a
-- pattern consists of domain values, functional symbols and variables.
-- Hence, a proof that a pattern is functional is a list of 'FunctionalProof'.
-- TODO: replace this datastructures with proper ones representing
-- both hypotheses and conclusions in the proof object.
data FunctionalProof level variable
    = FunctionalVariable variable
    -- ^Variables are functional as per Corollary 5.19
    -- https://arxiv.org/pdf/1705.06312.pdf#subsection.5.4
    -- |= ∃y . x = y
    | FunctionalDomainValue (Domain.Builtin ())
    -- ^ Domain value pattern without children are functional: they represent
    -- one value in the model.
    | FunctionalHead (SymbolOrAlias Object)
    -- ^Head of a total function, conforming to Definition 5.21
    -- https://arxiv.org/pdf/1705.06312.pdf#subsection.5.4
    | FunctionalStringLiteral StringLiteral
    -- ^A string literal is the repeated application of functional constructors.
    | FunctionalCharLiteral CharLiteral
    -- ^A char literal is a functional constructor without arguments.
  deriving Generic

deriving instance Eq variable => Eq (FunctionalProof level variable)
deriving instance Ord variable => Ord (FunctionalProof level variable)
deriving instance Show variable => Show (FunctionalProof level variable)

instance Hashable variable => Hashable (FunctionalProof level variable)

-- |'FunctionProof' is used for providing arguments that a pattern is
-- function-like.  Currently we only support arguments stating that a
-- pattern consists of domain values, functional and function symbols and
-- variables.
-- Hence, a proof that a pattern is function-like is a list of 'FunctionProof'.
-- TODO: replace this datastructures with proper ones representing
-- both hypotheses and conclusions in the proof object.
data FunctionProof level variable
    = FunctionProofFunctional (FunctionalProof Object variable)
    -- ^ A functional component is also function-like.
    | FunctionHead (SymbolOrAlias Object)
    -- ^Head of a partial function.

deriving instance Eq variable => Eq (FunctionProof level variable)
deriving instance Ord variable => Ord (FunctionProof level variable)
deriving instance Show variable => Show (FunctionProof level variable)

-- |'TotalProof' is used for providing arguments that a pattern is
-- total/not bottom.  Currently we only support arguments stating that a
-- pattern is functional or a constructor.
-- Hence, a proof that a pattern is total is a list of 'TotalProof'.
-- TODO: replace this datastructures with proper ones representing
-- both hypotheses and conclusions in the proof object.
data TotalProof level variable
    = TotalProofFunctional (FunctionalProof Object variable)
    -- ^A functional component is also total.
    | TotalHead (SymbolOrAlias Object)
    -- ^Head of a total symbol.

deriving instance Eq variable => Eq (TotalProof level variable)
deriving instance Ord variable => Ord (TotalProof level variable)
deriving instance Show variable => Show (TotalProof level variable)

-- |Used for providing arguments that a pattern is made of constructor-like
-- elements.
data ConstructorLikeProof = ConstructorLikeProof
  deriving (Eq, Show)

mapVariables
    :: (variable1 -> variable2)
    -> FunctionalProof Object variable1
    -> FunctionalProof Object variable2
mapVariables mapping =
    \case
        FunctionalVariable variable -> FunctionalVariable (mapping variable)
        FunctionalDomainValue value -> FunctionalDomainValue value
        FunctionalHead symbol -> FunctionalHead symbol
        FunctionalStringLiteral string -> FunctionalStringLiteral string
        FunctionalCharLiteral char -> FunctionalCharLiteral char
