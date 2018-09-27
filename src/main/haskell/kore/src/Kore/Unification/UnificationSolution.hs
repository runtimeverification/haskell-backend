{-|
Module      : Kore.Unification.UnificationSolution
Description : Datastructures and functionality for performing unification on
              Pure patterns
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Unification.UnificationSolution where

import Data.Functor.Foldable
import Kore.AST.Common
import Kore.AST.MLPatterns
import Kore.AST.PureML
import Kore.IndexedModule.MetadataTools
import Kore.Step.StepperAttributes
       ( StepperAttributes )
import Kore.Step.PatternAttributes
       ( FunctionalProof (..) )

type UnificationSubstitution level variable
    = [(variable level, PureMLPattern level variable)]

-- |'UnificationSolution' describes the solution of an unification problem,
-- consisting of the unified term and the set of constraints (equalities)
-- obtained during unification.
data UnificationSolution level variable = UnificationSolution
    { unificationSolutionTerm        :: !(PureMLPattern level variable)
    , unificationSolutionConstraints :: !(UnificationSubstitution level variable)
    }
  deriving (Eq, Show)

-- |'mapSubstitutionVariables' changes all the variables in the substitution
-- with the given function.
mapSubstitutionVariables
    :: (variableFrom level -> variableTo level)
    -> UnificationSubstitution level variableFrom
    -> UnificationSubstitution level variableTo
mapSubstitutionVariables variableMapper =
    map (mapVariable variableMapper)
  where
    mapVariable
        :: (variableFrom level -> variableTo level)
        -> (variableFrom level, PureMLPattern level variableFrom)
        -> (variableTo level, PureMLPattern level variableTo)
    mapVariable
        mapper
        (variable, patt)
      =
        (mapper variable, mapPatternVariables mapper patt)

-- |'unificationSolutionToPurePattern' packages an unification solution into
-- a 'CommonPurePattern' by transforming the constraints into a conjunction of
-- equalities and conjoining them with the unified term.
unificationSolutionToPurePattern
    :: SortedVariable variable
    => MetadataTools level StepperAttributes
    -> UnificationSolution level variable
    -> PureMLPattern level variable
unificationSolutionToPurePattern tools ucp =
    case unificationSolutionConstraints ucp of
        [] -> unifiedTerm
        (constraint:constraints) ->
            andPat unifiedTerm (foldr andEquals (equals constraint) constraints)
  where
    resultSort =
        getPatternResultSort (sortTools tools) (project unifiedTerm)
    unifiedTerm = unificationSolutionTerm ucp
    andEquals = andPat . equals
    andPat first second =
        Fix $ AndPattern And
            { andSort = resultSort
            , andFirst = first
            , andSecond = second
            }
    equals (var, p) =
        Fix $ EqualsPattern Equals
            { equalsOperandSort = sortedVariableSort var
            , equalsResultSort = resultSort
            , equalsFirst = Fix $ VariablePattern var
            , equalsSecond = p
            }

-- |'UnificationProof' is meant to represent proof term stubs for various
-- steps performed during unification
-- TODO: replace this datastructures with proper ones representing
-- both hypotheses and conclusions in the proof object.
data UnificationProof level variable
    = EmptyUnificationProof
    -- ^Empty proof (nothing to prove)
    | CombinedUnificationProof [UnificationProof level variable]
    -- ^Putting multiple proofs together
    | ConjunctionIdempotency (PureMLPattern level variable)
    -- ^Used to specify the reduction a/\a <-> a
    | Proposition_5_24_3
        [FunctionalProof level variable]
        (variable level)
        (PureMLPattern level variable)
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
        (PureMLPattern level variable)
        (PureMLPattern level variable)
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
  deriving (Eq, Show)

instance Semigroup (UnificationProof level variable) where
    (<>) proof1 proof2 = CombinedUnificationProof [proof1, proof2]

instance Monoid (UnificationProof level variable) where
    mempty = EmptyUnificationProof
    mconcat = CombinedUnificationProof
