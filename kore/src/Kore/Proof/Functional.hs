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
    ( Hashable
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug
import Kore.Internal.TermLike
    ( Builtin
    , Symbol
    )
import Kore.Sort
import Kore.Syntax.DomainValue
import Kore.Syntax.StringLiteral

-- |'FunctionalProof' is used for providing arguments that a pattern is
-- functional.  Currently we only support arguments stating that a
-- pattern consists of domain values, functional symbols and variables.
-- Hence, a proof that a pattern is functional is a list of 'FunctionalProof'.
-- TODO: replace this datastructures with proper ones representing
-- both hypotheses and conclusions in the proof object.
data FunctionalProof variable
    = FunctionalVariable variable
    -- ^Variables are functional as per Corollary 5.19
    -- https://arxiv.org/pdf/1705.06312.pdf#subsection.5.4
    -- |= ∃y . x = y
    | FunctionalBuiltin (Builtin ())
    -- ^ Builtin pattern without children are functional: they represent
    -- one value in the model.
    | FunctionalDomainValue (DomainValue Sort ())
    -- ^ Domain value pattern without children are functional: they represent
    -- one value in the model.
    | FunctionalHead Symbol
    -- ^Head of a total function, conforming to Definition 5.21
    -- https://arxiv.org/pdf/1705.06312.pdf#subsection.5.4
    | FunctionalStringLiteral StringLiteral
    -- ^A string literal is the repeated application of functional constructors.
  deriving (Eq, GHC.Generic, Ord, Show)

instance Hashable variable => Hashable (FunctionalProof variable)

instance SOP.Generic (FunctionalProof variable)

instance SOP.HasDatatypeInfo (FunctionalProof variable)

instance Debug variable => Debug (FunctionalProof variable)

instance (Debug variable, Diff variable) => Diff (FunctionalProof variable)

-- |'FunctionProof' is used for providing arguments that a pattern is
-- function-like.  Currently we only support arguments stating that a
-- pattern consists of domain values, functional and function symbols and
-- variables.
-- Hence, a proof that a pattern is function-like is a list of 'FunctionProof'.
-- TODO: replace this datastructures with proper ones representing
-- both hypotheses and conclusions in the proof object.
data FunctionProof variable
    = FunctionProofFunctional (FunctionalProof variable)
    -- ^ A functional component is also function-like.
    | FunctionHead Symbol
    -- ^Head of a partial function.

deriving instance Eq variable => Eq (FunctionProof variable)
deriving instance Ord variable => Ord (FunctionProof variable)
deriving instance Show variable => Show (FunctionProof variable)

-- |'TotalProof' is used for providing arguments that a pattern is
-- total/not bottom.  Currently we only support arguments stating that a
-- pattern is functional or a constructor.
-- Hence, a proof that a pattern is total is a list of 'TotalProof'.
-- TODO: replace this datastructures with proper ones representing
-- both hypotheses and conclusions in the proof object.
data TotalProof variable
    = TotalProofFunctional (FunctionalProof variable)
    -- ^A functional component is also total.
    | TotalHead Symbol
    -- ^Head of a total symbol.

deriving instance Eq variable => Eq (TotalProof variable)
deriving instance Ord variable => Ord (TotalProof variable)
deriving instance Show variable => Show (TotalProof variable)

-- |Used for providing arguments that a pattern is made of constructor-like
-- elements.
data ConstructorLikeProof = ConstructorLikeProof
    deriving (Eq, GHC.Generic, Show)

instance SOP.Generic ConstructorLikeProof

instance SOP.HasDatatypeInfo ConstructorLikeProof

instance Debug ConstructorLikeProof

instance Diff ConstructorLikeProof

mapVariables
    :: (variable1 -> variable2)
    -> FunctionalProof variable1
    -> FunctionalProof variable2
mapVariables mapping =
    \case
        FunctionalVariable variable -> FunctionalVariable (mapping variable)
        FunctionalBuiltin value -> FunctionalBuiltin value
        FunctionalDomainValue value -> FunctionalDomainValue value
        FunctionalHead symbol -> FunctionalHead symbol
        FunctionalStringLiteral string -> FunctionalStringLiteral string
