{-|
Module      : Data.Kore.Unification.Unifier
Description : Datastructures and functionality for performing unification on
              Pure patterns
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Kore.Unification.Unifier
    ( simplifyAnd
    , MetadataTools (..)
    , UnificationProof (..)
    , FunctionalProof (..)
    , unificationSolutionToPurePattern
    , UnificationSolution (..)
    , UnificationError (..)
    ) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.MLPatterns
import           Data.Kore.AST.PureML
import           Data.Kore.FixTraversals

import           Data.Fix
import           Data.Function            (on)
import           Data.List                (sortBy)

-- |'MetadataTools' defines a dictionary of functions which can be used to
-- access metadata needed during the unification process.
data MetadataTools level = MetadataTools
    { isConstructor    :: SymbolOrAlias level -> Bool
    , isFunctional     :: SymbolOrAlias level -> Bool
    , getArgumentSorts :: SymbolOrAlias level -> [Sort level]
    , getResultSort    :: SymbolOrAlias level -> Sort level
    }

-- |'UnificationSolution' describes the solution of an unification problem,
-- consisting of the unified term and the set of constraints (equalities)
-- obtained during unification.
data UnificationSolution level = UnificationSolution
    { unificationSolutionTerm        :: !(CommonPurePattern level)
    , unificationSolutionConstraints :: ![( Variable level
                                          , CommonPurePattern level)]
    }
  deriving (Eq)

-- |'unificationSolutionToPurePattern' packages an unification solution into
-- a 'CommonPurePattern' by transforming the constraints into a conjunction of
-- equalities and conjoining them with the unified term.
unificationSolutionToPurePattern
    :: MetadataTools level
    -> UnificationSolution level
    -> CommonPurePattern level
unificationSolutionToPurePattern tools ucp =
    case unificationSolutionConstraints ucp of
        [] -> unifiedTerm
        (constraint:constraints) ->
            andPat unifiedTerm (foldr andEquals (equals constraint) constraints)
  where
    resultSort = getPatternResultSort (getResultSort tools) (unFix unifiedTerm)
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
            { equalsOperandSort = variableSort var
            , equalsResultSort = resultSort
            , equalsFirst = Fix $ VariablePattern var
            , equalsSecond = p
            }

-- |'UnificationProof' is meant to represent proof term stubs for various
-- steps performed during unification
data UnificationProof level
    = UnificationProof
    -- ^Dummy constructor to specify dummy proof
    | ConjunctionIdempotency (CommonPurePattern level)
    -- ^Used to specify the reduction a/\a <-> a
    | Proposition_5_24_3
        [FunctionalProof level]
        (Variable level)
        (CommonPurePattern level)
    -- ^Used to specify the application of Proposition 5.24 (3)
    -- https://arxiv.org/pdf/1705.06312.pdf#subsection.5.4
    -- if ϕ and ϕ' are functional patterns, then
    -- |= (ϕ ∧ ϕ') = (ϕ ∧ (ϕ = ϕ'))
    | AndDistributionAndConstraintLifting
        (SymbolOrAlias level)
        [UnificationProof level]
    -- ^Used to specify both the application of the constructor axiom
    -- c(x1, .., xn) /\ c(y1, ..., yn) -> c(x1 /\ y1, ..., xn /\ yn)
    -- and of Proposition 5.12 (Constraint propagation) after unification:
    -- https://arxiv.org/pdf/1705.06312.pdf#subsection.5.2
    -- if ϕ is a predicate, then:
    -- |= c(ϕ1, ..., ϕi /\ ϕ, ..., ϕn) = c(ϕ1, ..., ϕi, ..., ϕn) /\ ϕ
  deriving (Eq)

-- ^'FunctionalProof' is used for providing arguments that a pattern is
-- functional.  Currently we only support arguments stating that a
-- pattern consists only of functional symbols and variables.
-- Hence, a proof that a pattern is functional is a list of 'FunctionalProof'.
data FunctionalProof level
    = FunctionalVariable (Variable level)
    -- ^Variables are functional as per Corollary 5.19
    -- https://arxiv.org/pdf/1705.06312.pdf#subsection.5.4
    -- |= ∃y . x = y
    | FunctionalHead (SymbolOrAlias level)
    -- ^Head of a total function, conforming to Definition 5.21
    -- https://arxiv.org/pdf/1705.06312.pdf#subsection.5.4
  deriving (Eq)

-- |'UnificationError' specifies various error cases encountered during
-- unification
data UnificationError level
    = ConstructorClash (SymbolOrAlias level) (SymbolOrAlias level)
    | NonConstructorHead (SymbolOrAlias level)
    | NonFunctionalHead (SymbolOrAlias level)
    | NonFunctionalPattern
    | UnsupportedPatterns
  deriving (Eq)

-- checks whether a pattern is functional or not
isFunctionalPattern
    :: MetadataTools level
    -> PureMLPattern level Variable
    -> Either (UnificationError level) [FunctionalProof level]
isFunctionalPattern tools = fixBottomUpVisitorM reduceM
  where
    reduceM (VariablePattern v) =
        Right [FunctionalVariable v]
    reduceM (ApplicationPattern ap) =
        if isFunctional tools patternHead
            then return (FunctionalHead patternHead : concat proofs)
            else Left (NonFunctionalHead patternHead)
      where
        patternHead = applicationSymbolOrAlias ap
        proofs = applicationChildren ap
    reduceM _ = Left NonFunctionalPattern

simplifyAnd
    :: MetadataTools level
    -> PureMLPattern level Variable
    -> Either
        (UnificationError level)
        (UnificationSolution level, UnificationProof level)
simplifyAnd tools =
    fixTopDownVisitor (preTransform tools) postTransform

-- Performs variable and equality checks and distributes the conjunction
-- to the children, creating sub-unification problems
preTransform
    :: MetadataTools level
    -> UnFixedPureMLPattern level Variable
    -> Either
        ( Either (UnificationError level) (UnificationSolution level
        , UnificationProof level))
        (UnFixedPureMLPattern level Variable)
preTransform tools (AndPattern ap) = if left == right
    then Left $ Right
        ( UnificationSolution
            { unificationSolutionTerm = left
            , unificationSolutionConstraints = []
            }
        , ConjunctionIdempotency left
        )
    else case (unFix left, unFix right) of
        (VariablePattern vp, _) ->
            Left (mlProposition_5_24_3 tools vp right)

        (_, VariablePattern vp) -> -- add commutativity here
            Left (mlProposition_5_24_3 tools vp left)
        (ApplicationPattern ap1, ApplicationPattern ap2) ->
            let
                head1 = applicationSymbolOrAlias ap1
                head2 = applicationSymbolOrAlias ap2
            in
                if isConstructor tools head1
                    then if head1 == head2
                        then Right
                            $ ApplicationPattern Application
                                { applicationSymbolOrAlias = head1
                                , applicationChildren =
                                    Fix . AndPattern
                                        <$> zipWith3 And
                                            (getArgumentSorts tools head1)
                                            (applicationChildren ap1)
                                            (applicationChildren ap2)
                                }
                        else if isConstructor tools head2
                            then Left $ Left (ConstructorClash head1 head2)
                            else Left $ Left (NonConstructorHead head2)
                    else Left $ Left (NonConstructorHead head1)
        _ -> Left $ Left UnsupportedPatterns
  where
    left = andFirst ap
    right = andSecond ap
preTransform _ _ = Left $ Left UnsupportedPatterns

-- applies Proposition 5.24 (3) which replaces x /\ phi with phi /\ x = phi
-- if phi is a functional pattern.
mlProposition_5_24_3
    :: MetadataTools level
    -> Variable level
    -- ^variable pattern
    -> PureMLPattern level Variable
    -- ^functional (term) pattern
    -> Either
        (UnificationError level)
        (UnificationSolution level, UnificationProof level)
mlProposition_5_24_3
    tools
    v
    functionalPattern
  = case isFunctionalPattern tools functionalPattern of
        Right functionalProof -> Right --Matching Logic 5.24 (3)
            ( UnificationSolution
                { unificationSolutionTerm        = functionalPattern
                , unificationSolutionConstraints = [ (v, functionalPattern) ]
                }
            , Proposition_5_24_3 functionalProof v functionalPattern
            )
        _ -> Left NonFunctionalPattern

-- returns from the recursion, building the unified term and
-- pushing up the constraints (substitution)
postTransform
    :: Pattern level Variable
        (Either
            (UnificationError level)
            (UnificationSolution level, UnificationProof level)
        )
    -> Either
        (UnificationError level)
        (UnificationSolution level, UnificationProof level)
postTransform (ApplicationPattern ap) =
    case sequenceA (applicationChildren ap) of
        Left err -> Left err
        Right children ->
            let (subSolutions, subProofs) = unzip children in
                Right
                    ( UnificationSolution
                        { unificationSolutionTerm = Fix $ ApplicationPattern ap
                            { applicationChildren =
                                    map unificationSolutionTerm subSolutions
                            }
                        , unificationSolutionConstraints =
                            sortBy (compare `on` fst)
                                (concatMap
                                    unificationSolutionConstraints
                                    subSolutions
                                )
                        }
                    , AndDistributionAndConstraintLifting
                        (applicationSymbolOrAlias ap)
                        subProofs
                    )
