{-|
Module      : Data.Kore.Unification.UnifierImpl
Description : Datastructures and functionality for performing unification on
              Pure patterns
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Kore.Unification.UnifierImpl where

import           Data.Kore.AST.Common
import           Data.Kore.AST.MLPatterns
import           Data.Kore.AST.PureML
import           Data.Kore.FixTraversals
import           Data.Kore.IndexedModule.MetadataTools
import           Data.Kore.Unification.Error

import           Control.Monad                         (foldM)
import           Data.Fix
import           Data.Function                         (on)
import           Data.List                             (groupBy, partition,
                                                        sortBy)

type UnificationSubstitution level = [(Variable level, CommonPurePattern level)]

-- |'UnificationSolution' describes the solution of an unification problem,
-- consisting of the unified term and the set of constraints (equalities)
-- obtained during unification.
data UnificationSolution level = UnificationSolution
    { unificationSolutionTerm        :: !(CommonPurePattern level)
    , unificationSolutionConstraints :: !(UnificationSubstitution level)
    }
  deriving (Eq, Show)

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
-- TODO: replace this datastructures with proper ones representing
-- both hypotheses and conclusions in the proof object.
data UnificationProof level
    = EmptyUnificationProof
    -- ^Empty proof (nothing to prove)
    | CombinedUnificationProof [UnificationProof level]
    -- ^Putting multiple proofs together
    | ConjunctionIdempotency (CommonPurePattern level)
    -- ^Used to specify the reduction a/\a <-> a
    | Proposition_5_24_3
        (FunctionalProof level)
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
    | SubstitutionMerge
        (Variable level)
        (CommonPurePattern level)
        (CommonPurePattern level)
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

-- ^'FunctionalProof' is used for providing arguments that a pattern is
-- functional.  Currently we only support arguments stating that a
-- pattern consists only of functional symbols and variables.
data FunctionalProof level
    = FunctionalVariable (Variable level)
    -- ^Variables are functional as per Corollary 5.19
    -- https://arxiv.org/pdf/1705.06312.pdf#subsection.5.4
    -- |= ∃y . x = y
    | FunctionalHeadAndChildren (SymbolOrAlias level) [FunctionalProof level]
    -- ^Head of a total function, conforming to Definition 5.21
    -- https://arxiv.org/pdf/1705.06312.pdf#subsection.5.4
  deriving (Eq, Show)

-- checks whether a pattern is functional or not
isFunctionalPattern
    :: MetadataTools level
    -> PureMLPattern level Variable
    -> Either (UnificationError level) (FunctionalProof level)
isFunctionalPattern tools (Fix (VariablePattern v)) 
  = Right (FunctionalVariable $ v)
isFunctionalPattern tools (Fix (ApplicationPattern ap))
  = if isFunctional tools patternHead
    then do
      functionalChildren <- mapM (isFunctionalPattern tools) patternChildren
      Right $ FunctionalHeadAndChildren patternHead functionalChildren
    else Left (NonFunctionalHead patternHead)
  where 
    patternHead = applicationSymbolOrAlias ap
    patternChildren = applicationChildren ap
isFunctionalPattern tools _ 
  = Left NonFunctionalPattern

simplifyAnds
    :: MetadataTools level
    -> [CommonPurePattern level]
    -> Either
        (UnificationError level)
        (UnificationSolution level, UnificationProof level)
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
    resultSort = getPatternResultSort (getResultSort tools) (unFix p)
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
        ( Either
            (UnificationError level)
            ( UnificationSolution level
            , UnificationProof level
            )
        )
        (UnFixedPureMLPattern level Variable)
preTransform tools (AndPattern (And _ left right)) = 
    if left == right
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
            if 
                 isConstructor tools head1 
              && isConstructor tools head2 
              && head1 == head2
            then Right $ ApplicationPattern Application
                  { applicationSymbolOrAlias = head1
                  , applicationChildren = 
                      Fix . AndPattern <$>
                        zipWith3 And 
                          (getArgumentSorts tools head1)
                          (applicationChildren ap1)
                          (applicationChildren ap2)
                  }
            else Left $ Left $
            if not (isConstructor tools head1)
            then NonConstructorHead head1
            else if not (isConstructor tools head2)
            then NonConstructorHead head2
            else if head1 /= head2
            then ConstructorClash head1 head2
            else error "This case should be unreachable"
              where                 
                head1 = applicationSymbolOrAlias ap1
                head2 = applicationSymbolOrAlias ap2
        _ -> Left $ Left UnsupportedPatterns
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
    :: UnificationSubstitution level -> [UnificationSubstitution level]
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
    :: MetadataTools level
    -> UnificationSubstitution level
    -> Either
        (UnificationError level)
        (UnificationSubstitution level, UnificationProof level)
solveGroupedSubstitution _ [] = Left EmptyPatternList
solveGroupedSubstitution tools ((x,p):subst) = do
    (solution, proof) <- simplifyAnds tools (p : map snd subst)
    return
        ( (x,unificationSolutionTerm solution)
          : unificationSolutionConstraints solution
        , proof)

instance Monoid (UnificationProof level) where
    mempty = EmptyUnificationProof
    mappend proof1 proof2 = CombinedUnificationProof [proof1, proof2]
    mconcat = CombinedUnificationProof

-- Takes a potentially non-normalized substitution,
-- and if it contains multiple assignments to the same variable,
-- it solves all such assignments.
-- As new assignments may be produced during the solving process,
-- `normalizeSubstitution` recursively calls itself until it stabilizes.
normalizeSubstitution
    :: MetadataTools level
    -> UnificationSubstitution level
    -> Either
        (UnificationError level)
        (UnificationSubstitution level, UnificationProof level)
normalizeSubstitution tools subst =
    if null nonSingletonSubstitutions
        then return (subst, EmptyUnificationProof)
        else do
            (subst', proof') <- mconcat <$>
                mapM (solveGroupedSubstitution tools) nonSingletonSubstitutions
            (finalSubst, proof) <-
                normalizeSubstitution tools
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

-- ^'unificationProcedure' atempts to simplify @t1 = t2@, assuming @t1@ and @t2@
-- are terms (functional patterns) to a substitution.
-- If successful, it also produces a proof of how the substitution was obtained.
-- If failing, it gives a 'UnificationError' reason for the failure.
unificationProcedure
    :: MetadataTools level
    -- ^functions yielding metadata for pattern heads
    -> CommonPurePattern level
    -- ^left-hand-side of unification
    -> CommonPurePattern level
    -> Either
        (UnificationError level)
        (UnificationSubstitution level, UnificationProof level)
unificationProcedure tools p1 p2
    | p1Sort /= p2Sort =
        Left (SortClash p1Sort p2Sort)
    | otherwise = do
        (solution, proof) <- simplifyAnd tools conjunct
        (normSubst, normProof) <-
            normalizeSubstitution tools (unificationSolutionConstraints solution)
        return (normSubst, CombinedUnificationProof [proof, normProof])
  where
    resultSort = getPatternResultSort (getResultSort tools)
    p1Sort =  resultSort (unFix p1)
    p2Sort =  resultSort (unFix p2)
    conjunct = Fix $ AndPattern And
        { andSort = p1Sort
        , andFirst = p1
        , andSecond = p2
        }
