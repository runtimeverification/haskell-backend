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

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.AST.MLPatterns
import Kore.AST.PureML
import Kore.ASTHelpers
       ( ApplicationSorts (..) )
import Kore.ASTUtils.SmartPatterns
       ( pattern StringLiteral_ )
import Kore.IndexedModule.MetadataTools
import Kore.Predicate.Predicate
       ( Predicate, makeTruePredicate )
import Kore.Step.PatternAttributes
       ( isFunctionalPattern )
import Kore.Step.StepperAttributes
import Kore.Unification.Error

type UnificationSubstitution level domain variable
    = [(variable level, PureMLPattern level domain variable)]

-- |'UnificationSolution' describes the solution of an unification problem,
-- consisting of the unified term and the set of constraints (equalities)
-- obtained during unification.
data UnificationSolution level domain variable = UnificationSolution
    { unificationSolutionTerm        :: !(PureMLPattern level domain variable)
    , unificationSolutionConstraints :: !(UnificationSubstitution level domain variable)
    }
  deriving (Eq, Show)

-- |'mapSubstitutionVariables' changes all the variables in the substitution
-- with the given function.
mapSubstitutionVariables
    :: (variableFrom level -> variableTo level)
    -> UnificationSubstitution level domain variableFrom
    -> UnificationSubstitution level domain variableTo
mapSubstitutionVariables variableMapper =
    map (mapVariable variableMapper)
  where
    mapVariable
        :: (variableFrom level -> variableTo level)
        -> (variableFrom level, PureMLPattern level domain variableFrom)
        -> (variableTo level, PureMLPattern level domain variableTo)
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
    -> UnificationSolution level domain variable
    -> PureMLPattern level domain variable
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

simplifyAnds
    :: ( Eq level
       , Ord (variable level)
       , SortedVariable variable
       , Show (variable level)
       )
    => MetadataTools level StepperAttributes
    -> [PureMLPattern level domain variable]
    -> Either
        (UnificationError level)
        (UnificationSolution level domain variable, ())
simplifyAnds _ [] = Left EmptyPatternList
simplifyAnds tools (p:ps) =
    foldM
        simplifyAnds'
        ( UnificationSolution
            { unificationSolutionTerm = p
            , unificationSolutionConstraints = []
            }
        , ()
        )
        ps
  where
    resultSort = getPatternResultSort (sortTools tools) (project p)
    simplifyAnds' (solution,_) pat = do
        let
            conjunct = Fix $ AndPattern And
                { andSort = resultSort
                , andFirst = unificationSolutionTerm solution
                , andSecond = pat
                }
        (solution', _) <- simplifyAnd tools conjunct
        return
            ( solution'
                { unificationSolutionConstraints =
                    unificationSolutionConstraints solution
                    ++ unificationSolutionConstraints solution'
                }
            , ()
            )

simplifyAnd
    :: ( Eq level
       , Ord (variable level)
       , Show (variable level)
       )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level domain variable
    -> Either
        (UnificationError level)
        (UnificationSolution level domain variable, ())
simplifyAnd tools =
    elgot postTransform (preTransform tools . project)

-- Performs variable and equality checks and distributes the conjunction
-- to the children, creating sub-unification problems
preTransform
    :: ( Eq level
       , Ord (variable level)
       , Show (variable level)
       )
    => MetadataTools level StepperAttributes
    -> UnFixedPureMLPattern level domain variable
    -> Either
        ( Either
            (UnificationError level)
            ( UnificationSolution level domain variable
            , ()
            )
        )
        (UnFixedPureMLPattern level domain variable)
preTransform tools (AndPattern ap) = if left == right
    then Left $ Right
        ( UnificationSolution
            { unificationSolutionTerm = left
            , unificationSolutionConstraints = []
            }
        , ()
        )
    else case project left of
        VariablePattern vp ->
            Left (mlProposition_5_24_3 tools vp right)
        p1 -> case project right of
            VariablePattern vp -> -- add commutativity here
                Left (mlProposition_5_24_3 tools vp left)
            DomainValuePattern (DomainValue _ dv2) ->
                case dv2 of
                    StringLiteral_ (StringLiteral sl2) ->
                        matchDomainValue tools p1 sl2
                    _ -> Left $ Left UnsupportedPatterns
            ApplicationPattern ap2 ->
                let
                    head2 = applicationSymbolOrAlias ap2
                in
                    if isConstructor (attributes tools head2)
                        then matchConstructor tools p1 head2 ap2
                        else Left $ Left $ NonConstructorHead head2
            _ -> Left $ Left UnsupportedPatterns
  where
    left = andFirst ap
    right = andSecond ap
preTransform _ _ = Left $ Left UnsupportedPatterns

matchDomainValue
    :: MetadataTools level StepperAttributes
    -> UnFixedPureMLPattern level domain variable
    -> String
    -> Either
        ( Either
            (UnificationError level)
            ( UnificationSolution level domain variable
            , ()
            )
        )
        (UnFixedPureMLPattern level domain variable)
matchDomainValue _ (DomainValuePattern (DomainValue _ dv1)) sl2 =
    case dv1 of
        StringLiteral_ (StringLiteral sl1) ->
            Left $ Left
                (PatternClash (DomainValueClash sl1) (DomainValueClash sl2))
        _ ->  Left $ Left UnsupportedPatterns
matchDomainValue tools (ApplicationPattern ap1) sl2
    | isConstructor (attributes tools head1) =
        Left $ Left (PatternClash (HeadClash head1) (DomainValueClash sl2))
    | otherwise = Left $ Left $ NonConstructorHead head1
  where
    head1 = applicationSymbolOrAlias ap1
matchDomainValue _ _ _ = Left $ Left UnsupportedPatterns

matchConstructor
    :: MetadataTools level StepperAttributes
    -> UnFixedPureMLPattern level domain variable
    -> SymbolOrAlias level
    -> Application level (PureMLPattern level domain variable)
    -> Either
        ( Either
            (UnificationError level)
            ( UnificationSolution level domain variable
            , ()
            )
        )
        (UnFixedPureMLPattern level domain variable)
matchConstructor _ (DomainValuePattern (DomainValue _ dv1)) head2 _ =
    case dv1 of
        (StringLiteral_ (StringLiteral sl1)) ->
            Left $ Left (PatternClash (DomainValueClash sl1) (HeadClash head2))
        _ -> Left $ Left UnsupportedPatterns
matchConstructor tools (ApplicationPattern ap1) head2 ap2
    | isConstructor (attributes tools head1) =
        if head1 == head2
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
            else Left $ Left
                    (PatternClash
                        (HeadClash head1)
                        (HeadClash head2)
                    )
    | otherwise = Left $ Left $ NonConstructorHead head1
  where
    head1 = applicationSymbolOrAlias ap1
matchConstructor _ _ _ _ = Left $ Left UnsupportedPatterns                                


-- applies Proposition 5.24 (3) which replaces x /\ phi with phi /\ x = phi
-- if phi is a functional pattern.
mlProposition_5_24_3
    :: Show (variable level)
    => MetadataTools level StepperAttributes
    -> variable level
    -- ^variable pattern
    -> PureMLPattern level domain variable
    -- ^functional (term) pattern
    -> Either
        (UnificationError level)
        (UnificationSolution level domain variable, ())
mlProposition_5_24_3
    tools
    v
    functionalPattern
  = case isFunctionalPattern tools functionalPattern of
        Right _ -> Right --Matching Logic 5.24 (3)
            ( UnificationSolution
                { unificationSolutionTerm        = functionalPattern
                , unificationSolutionConstraints = [ (v, functionalPattern) ]
                }
            , ()
            )
        _ -> Left NonFunctionalPattern

-- returns from the recursion, building the unified term and
-- pushing up the constraints (substitution)
postTransform
    :: Pattern level domain variable
        (Either
            (UnificationError level)
            ( UnificationSolution level domain variable
            , ()
            )
        )
    -> Either
        (UnificationError level)
        (UnificationSolution level domain variable, ())
postTransform (ApplicationPattern ap) = do
    children <- sequenceA (applicationChildren ap)
    let (subSolutions, _) = unzip children
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
        , ()
        )
postTransform _ = error "Unexpected, non-application, pattern."

groupSubstitutionByVariable
    :: Ord (variable level)
    => UnificationSubstitution level domain variable
    -> [UnificationSubstitution level domain variable]
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
    :: ( Eq level
       , Ord (variable level)
       , SortedVariable variable
       , Show (variable level)
       )
    => MetadataTools level StepperAttributes
    -> UnificationSubstitution level domain variable
    -> Either
        (UnificationError level)
        (UnificationSubstitution level domain variable, ())
solveGroupedSubstitution _ [] = Left EmptyPatternList
solveGroupedSubstitution tools ((x,p):subst) = do
    (solution, _) <- simplifyAnds tools (p : map snd subst)
    return
        ( (x,unificationSolutionTerm solution)
          : unificationSolutionConstraints solution
        , ())

-- |Takes a potentially non-normalized substitution,
-- and if it contains multiple assignments to the same variable,
-- it solves all such assignments.
-- As new assignments may be produced during the solving process,
-- `normalizeSubstitutionDuplication` recursively calls itself until it
-- stabilizes.
normalizeSubstitutionDuplication
    :: ( Eq level
       , Ord (variable level)
       , SortedVariable variable
       , Show (variable level)
       )
    => MetadataTools level StepperAttributes
    -> UnificationSubstitution level domain variable
    -> Either
        (UnificationError level)
        ( UnificationSubstitution level domain variable
        , ()
        )
normalizeSubstitutionDuplication tools subst =
    if null nonSingletonSubstitutions
        then return (subst, ())
        else do
            (subst', _) <- mconcat <$>
                mapM (solveGroupedSubstitution tools) nonSingletonSubstitutions
            (finalSubst, _) <-
                normalizeSubstitutionDuplication tools
                    (concat singletonSubstitutions
                     ++ subst'
                    )
            return
                ( finalSubst
                , ()
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
        , MetaOrObject level
        , Show (variable level)
        )
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> PureMLPattern level domain variable
    -- ^left-hand-side of unification
    -> PureMLPattern level domain variable
    -> Either
        -- TODO: Consider using a false predicate instead of a Left error
        (UnificationError level)
        ( UnificationSubstitution level domain variable
        , Predicate level domain variable
        , ()
        )
unificationProcedure tools p1 p2
    | p1Sort /= p2Sort =
        Left (SortClash p1Sort p2Sort)
    | otherwise = do
        (solution, _) <- simplifyAnd tools conjunct
        (normSubst, _) <-
            normalizeSubstitutionDuplication
                tools (unificationSolutionConstraints solution)
        return
            ( normSubst
            -- TODO: Put something sensible here.
            , makeTruePredicate
            , ()
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
