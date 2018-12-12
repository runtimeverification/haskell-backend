{-|
Module      : Kore.Unification.Data
Description : Datastructures and functionality for performing unification on
              Pure patterns
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Unification.Data
    ( UnificationProof (..)
    ) where

import GHC.Generics
       ( Generic )


import Kore.AST.Pure
import Kore.Proof.Functional
       ( FunctionalProof (..) )
import Kore.Reflect
       ( Reflectable )
import Kore.Step.Pattern

-- |'UnificationProof' is meant to represent proof term stubs for various
-- steps performed during unification
-- TODO: replace this datastructures with proper ones representing
-- both hypotheses and conclusions in the proof object.
data UnificationProof level variable
    = EmptyUnificationProof
    -- ^Empty proof (nothing to prove)
    | CombinedUnificationProof [UnificationProof level variable]
    -- ^Putting multiple proofs together
    | ConjunctionIdempotency (StepPattern level variable)
    -- ^Used to specify the reduction a/\a <-> a
    | Proposition_5_24_3
        [FunctionalProof level variable]
        (variable level)
        (StepPattern level variable)
    -- ^Used to specify the application of Proposition 5.24 (3)
    -- https://arxiv.org/pdf/1705.06312.pdf#subsection.5.4
    -- if ϕ and ϕ' are functional patterns, then
    -- |= (ϕ ∧ ϕ') = (ϕ ∧ (ϕ = ϕ'))
    | AndDistributionAndConstraintLifting
        (SymbolOrAlias level)
        [UnificationProof level variable]
    -- ^Used to specify both the application of the constructor axiom
    -- c(x1, .., xn) /\ c(y1, ..., yn) -> c(x1 /\ y1, ..., xn /\ yn)
    -- and of Proposition 5.12 (Constraint propagation) after unification:
    -- https://arxiv.org/pdf/1705.06312.pdf#subsection.5.2
    -- if ϕ is a predicate, then:
    -- |= c(ϕ1, ..., ϕi /\ ϕ, ..., ϕn) = c(ϕ1, ..., ϕi, ..., ϕn) /\ ϕ
    | SubstitutionMerge
        (variable level)
        (StepPattern level variable)
        (StepPattern level variable)
    -- ^Specifies the merging of (x = t1) /\ (x = t2) into x = (t1 /\ t2)
    -- Semantics of K, 7.7.1:
    -- (Equality Elimination). |- (ϕ1 = ϕ2) → (ψ[ϕ1/v] → ψ[ϕ2/v])
    -- if we instantiate it using  ϕ1 = x, ϕ2 = y and ψ = (v = t2), we get
    -- |- x = t1 -> ((x = t2) -> (t1 = t2))
    -- by boolean manipulation, we can get
    -- |- (x = t1) /\ (x = t2) -> ((x = t1) /\ (t1 = t2))
    -- By some ??magic?? similar to Proposition 5.12
    -- ((x = t1) /\ (t1 = t2)) = (x = (t1 /\ (t1 = t2)))
    -- then, applying Proposition 5.24(3), this further gets to
    -- (x = (t1 /\ t2))
  deriving (Eq, Generic, Show)

instance
    Reflectable (variable level)
    => Reflectable (UnificationProof level variable)

instance Semigroup (UnificationProof level variable) where
    (<>) proof1 proof2 = CombinedUnificationProof [proof1, proof2]

instance Monoid (UnificationProof level variable) where
    mempty = EmptyUnificationProof
    mconcat = CombinedUnificationProof
