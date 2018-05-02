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
    foldr
        (andEquals
            (getPatternResultSort (getResultSort tools) (unFix unifiedTerm)))
        unifiedTerm
        (unificationSolutionConstraints ucp)
  where
    unifiedTerm = unificationSolutionTerm ucp
    andEquals sort (var, p) second = Fix $ AndPattern And
        { andSort = sort
        , andFirst = Fix $ EqualsPattern Equals
            { equalsOperandSort = variableSort var
            , equalsResultSort = sort
            , equalsFirst = Fix $ VariablePattern var
            , equalsSecond = p
            }
        , andSecond = second
        }

-- |'UnificationProof' is meant to represent proof term stubs for various
-- steps performed during unification
data UnificationProof level
    = UnificationProof -- ^dummy constructor to specify dummy proof
    | ConjunctionIdempotency (CommonPurePattern level)
    -- ^used to specify the reduction a/\a <-> a
    | Proposition5243
        [FunctionalProof level]
        (Variable level)
        (CommonPurePattern level)
    -- ^used to specify the application of Proposition 5.24 (3)
    | AndDistributionAndConstraintLifting
        (SymbolOrAlias level)
        [UnificationProof level]
    -- ^Used to specify both the application of the constructor axiom and the
    -- lifting of the constraints.
  deriving (Eq)

data FunctionalProof level
    = FunctionalVariable (Variable level)
    | FunctionalHead (SymbolOrAlias level)
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
            Left (mlProposition5243 tools vp right)

        (_, VariablePattern vp) -> -- add commutativity here
            Left (mlProposition5243 tools vp left)
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

-- applies Proposition 5.24 (3) which replaces x /\ phi with phi /\ x = phi
-- if phi is a functional pattern.
mlProposition5243
    :: MetadataTools level
    -> Variable level
    -- ^variable pattern
    -> PureMLPattern level Variable
    -- ^functional (term) pattern
    -> Either
        (UnificationError level)
        (UnificationSolution level, UnificationProof level)
mlProposition5243
    tools
    v
    functionalPattern
  = case isFunctionalPattern tools functionalPattern of
        Right functionalProof -> Right --Matching Logic 5.24 (3)
            ( UnificationSolution
                { unificationSolutionTerm        = functionalPattern
                , unificationSolutionConstraints = [ (v, functionalPattern) ]
                }
            , Proposition5243 functionalProof v functionalPattern
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
