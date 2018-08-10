{-|
Module      : Kore.Unification.UnifierImpl
Description : Datastructures and functionality for performing unification on
              Pure patterns
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Unification.UnifierImpl where

import Control.Monad
       ( foldM )
import Data.Function
       ( on )
import Data.Functor.Foldable
import Data.List
       ( groupBy, partition, sortBy )

import Data.Functor.Traversable
import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.AST.MLPatterns
import Kore.AST.PureML
import Kore.ASTHelpers
       (ApplicationSorts (..))
import Kore.IndexedModule.MetadataTools
import Kore.Predicate.Predicate
       ( Predicate, makeTruePredicate )
import Kore.Step.StepperAttributes
import Kore.Unification.Error

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

{-# ANN simplifyUnificationProof ("HLint: ignore Use record patterns" :: String) #-}
simplifyUnificationProof
    :: UnificationProof level variable
    -> UnificationProof level variable
simplifyUnificationProof EmptyUnificationProof = EmptyUnificationProof
simplifyUnificationProof (CombinedUnificationProof []) =
    EmptyUnificationProof
simplifyUnificationProof (CombinedUnificationProof [a]) =
    simplifyUnificationProof a
simplifyUnificationProof (CombinedUnificationProof items) =
    case simplifyCombinedItems items of
        []  -> EmptyUnificationProof
        [a] -> a
        as  -> CombinedUnificationProof as
simplifyUnificationProof a@(ConjunctionIdempotency _) = a
simplifyUnificationProof a@(Proposition_5_24_3 _ _ _) = a
simplifyUnificationProof
    (AndDistributionAndConstraintLifting symbolOrAlias unificationProof)
  =
    AndDistributionAndConstraintLifting
        symbolOrAlias
        (simplifyCombinedItems unificationProof)
simplifyUnificationProof a@(SubstitutionMerge _ _ _) = a

simplifyCombinedItems
    :: [UnificationProof level variable] -> [UnificationProof level variable]
simplifyCombinedItems =
    foldr (addContents . simplifyUnificationProof) []
  where
    addContents
        :: UnificationProof level variable
        -> [UnificationProof level variable]
        -> [UnificationProof level variable]
    addContents EmptyUnificationProof  proofItems           = proofItems
    addContents (CombinedUnificationProof items) proofItems =
        items ++ proofItems
    addContents other proofItems = other : proofItems

-- |'FunctionalProof' is used for providing arguments that a pattern is
-- functional.  Currently we only support arguments stating that a
-- pattern consists only of functional symbols and variables.
-- Hence, a proof that a pattern is functional is a list of 'FunctionalProof'.
-- TODO: replace this datastructures with proper ones representing
-- both hypotheses and conclusions in the proof object.
data FunctionalProof level variable
    = FunctionalVariable (variable level)
    -- ^Variables are functional as per Corollary 5.19
    -- https://arxiv.org/pdf/1705.06312.pdf#subsection.5.4
    -- |= ∃y . x = y
    | FunctionalHead (SymbolOrAlias level)
    -- ^Head of a total function, conforming to Definition 5.21
    -- https://arxiv.org/pdf/1705.06312.pdf#subsection.5.4
  deriving (Eq, Show)

{--| 'mapFunctionalProofVariables' replaces all variables in a 'FunctionalProof'
using the provided mapping.
--}
mapFunctionalProofVariables
    :: (variableFrom level -> variableTo level)
    -> FunctionalProof level variableFrom
    -> FunctionalProof level variableTo
mapFunctionalProofVariables mapper (FunctionalVariable variable) =
    FunctionalVariable (mapper variable)
mapFunctionalProofVariables _ (FunctionalHead functionalHead) =
    FunctionalHead functionalHead

-- checks whether a pattern is functional or not
isFunctionalPattern
    :: MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> Either (UnificationError level) [FunctionalProof level variable]
isFunctionalPattern tools = fixBottomUpVisitorM reduceM
  where
    reduceM (VariablePattern v) =
        Right [FunctionalVariable v]
    reduceM (ApplicationPattern ap) =
        if isFunctional (attributes tools patternHead)
            then return (FunctionalHead patternHead : concat proofs)
            else Left (NonFunctionalHead patternHead)
      where
        patternHead = applicationSymbolOrAlias ap
        proofs = applicationChildren ap
    reduceM _ = Left NonFunctionalPattern

simplifyAnds
    :: (Eq level, Ord (variable level), SortedVariable variable)
    => MetadataTools level StepperAttributes
    -> [PureMLPattern level variable]
    -> Either
        (UnificationError level)
        (UnificationSolution level variable, UnificationProof level variable)
simplifyAnds _ [] = Left EmptyPatternList
simplifyAnds tools (p:ps) =
    foldM
        simplifyAnds'
        ( UnificationSolution
            { unificationSolutionTerm = p
            , unificationSolutionConstraints = []
            }
        , EmptyUnificationProof
        )
        ps
  where
    resultSort = getPatternResultSort (sortTools tools) (project p)
    simplifyAnds' (solution,proof) pat = do
        let
            conjunct = Fix $ AndPattern And
                { andSort = resultSort
                , andFirst = unificationSolutionTerm solution
                , andSecond = pat
                }
        (solution', proof') <- simplifyAnd tools conjunct
        return
            ( solution'
                { unificationSolutionConstraints =
                    unificationSolutionConstraints solution
                    ++ unificationSolutionConstraints solution'
                }
            , CombinedUnificationProof [proof, proof']
            )

simplifyAnd
    :: (Eq level, Ord (variable level))
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> Either
        (UnificationError level)
        (UnificationSolution level variable, UnificationProof level variable)
simplifyAnd tools =
    fixTopDownVisitor (preTransform tools) postTransform

-- Performs variable and equality checks and distributes the conjunction
-- to the children, creating sub-unification problems
preTransform
    :: (Eq level, Ord (variable level))
    => MetadataTools level StepperAttributes
    -> UnFixedPureMLPattern level variable
    -> Either
        ( Either
            (UnificationError level)
            ( UnificationSolution level variable
            , UnificationProof level variable
            )
        )
        (UnFixedPureMLPattern level variable)
preTransform tools (AndPattern ap) = if left == right
    then Left $ Right
        ( UnificationSolution
            { unificationSolutionTerm = left
            , unificationSolutionConstraints = []
            }
        , ConjunctionIdempotency left
        )
    else case (project left, project right) of
        (VariablePattern vp, _) ->
            Left (mlProposition_5_24_3 tools vp right)

        (_, VariablePattern vp) -> -- add commutativity here
            Left (mlProposition_5_24_3 tools vp left)
        (ApplicationPattern ap1, ApplicationPattern ap2) ->
            let
                head1 = applicationSymbolOrAlias ap1
                head2 = applicationSymbolOrAlias ap2
            in
                if isConstructor (attributes tools head1)
                    then if head1 == head2
                        then Right
                            $ ApplicationPattern Application
                                { applicationSymbolOrAlias = head1
                                , applicationChildren =
                                    Fix . AndPattern
                                        <$> zipWith3 And
                                            (applicationSortsOperands
                                                (sortTools tools head1)
                                            )
                                            (applicationChildren ap1)
                                            (applicationChildren ap2)
                                }
                        else if isConstructor (attributes tools head2)
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
    :: MetadataTools level StepperAttributes
    -> variable level
    -- ^variable pattern
    -> PureMLPattern level variable
    -- ^functional (term) pattern
    -> Either
        (UnificationError level)
        (UnificationSolution level variable, UnificationProof level variable)
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
    :: Pattern level variable
        (Either
            (UnificationError level)
            ( UnificationSolution level variable
            , UnificationProof level variable
            )
        )
    -> Either
        (UnificationError level)
        (UnificationSolution level variable, UnificationProof level variable)
postTransform (ApplicationPattern ap) = do
    children <- sequenceA (applicationChildren ap)
    let (subSolutions, subProofs) = unzip children
    return
        ( UnificationSolution
            { unificationSolutionTerm = Fix $ ApplicationPattern ap
                { applicationChildren =
                        map unificationSolutionTerm subSolutions
                }
            , unificationSolutionConstraints =
                concatMap
                    unificationSolutionConstraints
                    subSolutions
            }
        , AndDistributionAndConstraintLifting
            (applicationSymbolOrAlias ap)
            subProofs
        )
postTransform _ = error "Unexpected, non-application, pattern."

groupSubstitutionByVariable
    :: Ord (variable level)
    => UnificationSubstitution level variable
    -> [UnificationSubstitution level variable]
groupSubstitutionByVariable =
    groupBy ((==) `on` fst) . sortBy (compare `on` fst) . map sortRenaming
  where
    sortRenaming (var, Fix (VariablePattern var'))
        | var' < var = (var', Fix (VariablePattern var))
    sortRenaming eq = eq

-- simplifies x = t1 /\ x = t2 /\ ... /\ x = tn by transforming it into
-- x = ((t1 /\ t2) /\ (..)) /\ tn
-- then recursively reducing that to finally get x = t /\ subst
solveGroupedSubstitution
    :: (Eq level, Ord (variable level), SortedVariable variable)
    => MetadataTools level StepperAttributes
    -> UnificationSubstitution level variable
    -> Either
        (UnificationError level)
        (UnificationSubstitution level variable, UnificationProof level variable)
solveGroupedSubstitution _ [] = Left EmptyPatternList
solveGroupedSubstitution tools ((x,p):subst) = do
    (solution, proof) <- simplifyAnds tools (p : map snd subst)
    return
        ( (x,unificationSolutionTerm solution)
          : unificationSolutionConstraints solution
        , proof)

instance Monoid (UnificationProof level variable) where
    mempty = EmptyUnificationProof
    mappend proof1 proof2 = CombinedUnificationProof [proof1, proof2]
    mconcat = CombinedUnificationProof

-- |Takes a potentially non-normalized substitution,
-- and if it contains multiple assignments to the same variable,
-- it solves all such assignments.
-- As new assignments may be produced during the solving process,
-- `normalizeSubstitutionDuplication` recursively calls itself until it
-- stabilizes.
normalizeSubstitutionDuplication
    :: (Eq level, Ord (variable level), SortedVariable variable)
    => MetadataTools level StepperAttributes
    -> UnificationSubstitution level variable
    -> Either
        (UnificationError level)
        ( UnificationSubstitution level variable
        , UnificationProof level variable
        )
normalizeSubstitutionDuplication tools subst =
    if null nonSingletonSubstitutions
        then return (subst, EmptyUnificationProof)
        else do
            (subst', proof') <- mconcat <$>
                mapM (solveGroupedSubstitution tools) nonSingletonSubstitutions
            (finalSubst, proof) <-
                normalizeSubstitutionDuplication tools
                    (concat singletonSubstitutions
                     ++ subst'
                    )
            return
                ( finalSubst
                , CombinedUnificationProof
                    [ proof'
                    , proof
                    ]
                )
  where
    groupedSubstitution = groupSubstitutionByVariable subst
    isSingleton [_] = True
    isSingleton _   = False
    (singletonSubstitutions, nonSingletonSubstitutions) =
        partition isSingleton groupedSubstitution

-- |'unificationProcedure' atempts to simplify @t1 = t2@, assuming @t1@ and @t2@
-- are terms (functional patterns) to a substitution.
-- If successful, it also produces a proof of how the substitution was obtained.
-- If failing, it gives a 'UnificationError' reason for the failure.
unificationProcedure
    ::  ( SortedVariable variable
        , Ord (variable level)
        , MetaOrObject level)
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> PureMLPattern level variable
    -- ^left-hand-side of unification
    -> PureMLPattern level variable
    -> Either
        -- TODO: Consider using a false predicate instead of a Left error
        (UnificationError level)
        ( UnificationSubstitution level variable
        , Predicate level variable
        , UnificationProof level variable
        )
unificationProcedure tools p1 p2
    | p1Sort /= p2Sort =
        Left (SortClash p1Sort p2Sort)
    | otherwise = do
        (solution, proof) <- simplifyAnd tools conjunct
        (normSubst, normProof) <-
            normalizeSubstitutionDuplication
                tools (unificationSolutionConstraints solution)
        return
            ( normSubst
            -- TODO: Put something sensible here.
            , makeTruePredicate
            , simplifyUnificationProof
                (CombinedUnificationProof [proof, normProof])
            )
  where
    resultSort = getPatternResultSort (sortTools tools)
    p1Sort =  resultSort (project p1)
    p2Sort =  resultSort (project p2)
    conjunct = Fix $ AndPattern And
        { andSort = p1Sort
        , andFirst = p1
        , andSecond = p2
        }
