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
    , Kore.Unification.Data.mapVariables
    ) where

import Data.Hashable
       ( Hashable )
import GHC.Generics
       ( Generic )

import           Kore.AST.Pure
import           Kore.Proof.Functional
                 ( FunctionalProof (..) )
import qualified Kore.Proof.Functional as Proof.Functional
import           Kore.Step.TermLike
                 ( TermLike )
import qualified Kore.Step.TermLike as TermLike

-- |'UnificationProof' is meant to represent proof term stubs for various
-- steps performed during unification
-- TODO: replace this datastructures with proper ones representing
-- both hypotheses and conclusions in the proof object.
data UnificationProof level variable
    = EmptyUnificationProof
    -- ^Empty proof (nothing to prove)
    | CombinedUnificationProof [UnificationProof level variable]
    -- ^Putting multiple proofs together
    | ConjunctionIdempotency (TermLike variable)
    -- ^Used to specify the reduction a/\a <-> a
    | Proposition_5_24_3
        [FunctionalProof Object variable]
        variable
        (TermLike variable)
    -- ^Used to specify the application of Proposition 5.24 (3)
    -- https://arxiv.org/pdf/1705.06312.pdf#subsection.5.4
    -- if ϕ and ϕ' are functional patterns, then
    -- |= (ϕ ∧ ϕ') = (ϕ ∧ (ϕ = ϕ'))
    | AndDistributionAndConstraintLifting
        (SymbolOrAlias Object)
        [UnificationProof Object variable]
    -- ^Used to specify both the application of the constructor axiom
    -- c(x1, .., xn) /\ c(y1, ..., yn) -> c(x1 /\ y1, ..., xn /\ yn)
    -- and of Proposition 5.12 (Constraint propagation) after unification:
    -- https://arxiv.org/pdf/1705.06312.pdf#subsection.5.2
    -- if ϕ is a predicate, then:
    -- |= c(ϕ1, ..., ϕi /\ ϕ, ..., ϕn) = c(ϕ1, ..., ϕi, ..., ϕn) /\ ϕ
    | SubstitutionMerge
        variable
        (TermLike variable)
        (TermLike variable)
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
  deriving Generic

deriving instance Eq variable => Eq (UnificationProof level variable)
deriving instance Ord variable => Ord (UnificationProof level variable)
deriving instance Show variable => Show (UnificationProof level variable)

instance Hashable variable => Hashable (UnificationProof level variable)

instance Semigroup (UnificationProof level variable) where
    (<>) proof1 proof2 = CombinedUnificationProof [proof1, proof2]

instance Monoid (UnificationProof level variable) where
    mempty = EmptyUnificationProof
    mconcat = CombinedUnificationProof

mapVariables
    :: Ord variable2
    => (variable1 -> variable2)
    -> UnificationProof Object variable1
    -> UnificationProof Object variable2
mapVariables mapping = mapVariablesWorker
  where
    mapVariablesWorker =
        \case
            EmptyUnificationProof -> EmptyUnificationProof
            CombinedUnificationProof proofs ->
                CombinedUnificationProof (map mapVariablesWorker proofs)
            ConjunctionIdempotency patt ->
                ConjunctionIdempotency (TermLike.mapVariables mapping patt)
            Proposition_5_24_3 proofs variable patt ->
                Proposition_5_24_3
                    (map (Proof.Functional.mapVariables mapping) proofs)
                    (mapping variable)
                    (TermLike.mapVariables mapping patt)
            AndDistributionAndConstraintLifting symbol proofs ->
                AndDistributionAndConstraintLifting
                    symbol
                    (map mapVariablesWorker proofs)
            SubstitutionMerge variable patt1 patt2 ->
                SubstitutionMerge
                    (mapping variable)
                    (TermLike.mapVariables mapping patt1)
                    (TermLike.mapVariables mapping patt2)
