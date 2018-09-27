{-|
Module      : Kore.Unification.UnifierImpl
Description : Datastructures and functionality for performing unification on
              Pure patterns
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Unification.UnifierImpl where

import Control.Error.Util
       ( note )
import Control.Monad
       ( foldM )
import Control.Monad.Counter
       ( MonadCounter )
import Control.Monad.Except
       ( ExceptT(..)  )
import Control.Monad.Trans.Except
       ( throwE )
import Data.Function
       ( on )
import Data.Functor.Foldable
import Data.List
       ( groupBy, partition, sortBy )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
import           Kore.ASTUtils.SmartPatterns
import           Kore.IndexedModule.MetadataTools
import qualified Kore.Predicate.Predicate as Predicate
                 ( isFalse )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), top, bottom )
import qualified Kore.Step.ExpandedPattern as PredicateSubstitution
                 ( PredicateSubstitution (..) )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern )
import           Kore.Step.StepperAttributes
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Unification.Data
import           Kore.Unification.Error
import           Kore.Variables.Fresh
                 ( FreshVariable )

import {-# SOURCE #-} Kore.Step.Substitution
                      ( mergePredicatesAndSubstitutions )
import {-# SOURCE #-} Kore.Step.Simplification.AndTerms
                      ( termUnification )

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

simplifyAnds
    :: forall level variable m
     . ( MetaOrObject level
       , Eq level
       , Ord (variable level)
       , Ord (variable Meta)
       , Ord (variable Object)
       , SortedVariable variable
       , Show (variable level)
       , Hashable variable
       , FreshVariable variable
       , MonadCounter m
       )
    => MetadataTools level StepperAttributes
    -> [PureMLPattern level variable]
    -> ExceptT
        UnificationError
        m
        ( ExpandedPattern level variable
        , UnificationProof level variable
        )
simplifyAnds _ [] = throwE UnsupportedPatterns
simplifyAnds tools patterns = do
     result <- foldM
        simplifyAnds'
        ExpandedPattern.top
        patterns
     if Predicate.isFalse . ExpandedPattern.predicate $ result
         then return ( ExpandedPattern.bottom, EmptyUnificationProof )
         else return ( result, EmptyUnificationProof )
  where
    simplifyAnds'
        :: ExpandedPattern level variable
        -> PureMLPattern level variable
        -> ExceptT
            UnificationError
            m
            ( ExpandedPattern level variable )
    simplifyAnds' intermediate (And_ _ lhs rhs) =
        foldM simplifyAnds' intermediate [lhs, rhs]
    simplifyAnds' intermediate pat = do
        (result, _) <- ExceptT . sequence
            $ note UnsupportedPatterns
            $ termUnification tools (ExpandedPattern.term intermediate) pat
        (predSubst, _) <- mergePredicatesAndSubstitutions tools
          [ ExpandedPattern.predicate result, ExpandedPattern.predicate intermediate ]
          [ ExpandedPattern.substitution result, ExpandedPattern.substitution intermediate ]

        return $ ExpandedPattern.ExpandedPattern
            ( ExpandedPattern.term result )
            ( PredicateSubstitution.predicate predSubst )
            ( PredicateSubstitution.substitution predSubst )


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
    :: ( MetaOrObject level
       , Eq level
       , Ord (variable level)
       , Ord (variable Meta)
       , Ord (variable Object)
       , SortedVariable variable
       , Show (variable level)
       , Hashable variable
       , FreshVariable variable
       , MonadCounter m
       )
    => MetadataTools level StepperAttributes
    -> UnificationSubstitution level variable
    -> ExceptT
        UnificationError
        m
        ( UnificationSubstitution level variable
        , UnificationProof level variable
        )
solveGroupedSubstitution _ [] = throwE UnsupportedPatterns
solveGroupedSubstitution tools ((x,p):subst) = do
    (solution, proof) <- simplifyAnds tools (p : map snd subst)
    return
        ( (x, ExpandedPattern.term solution)
          : ExpandedPattern.substitution solution
        , proof)

-- |Takes a potentially non-normalized substitution,
-- and if it contains multiple assignments to the same variable,
-- it solves all such assignments.
-- As new assignments may be produced during the solving process,
-- `normalizeSubstitutionDuplication` recursively calls itself until it
-- stabilizes.
normalizeSubstitutionDuplication
    :: ( MetaOrObject level
       , Eq level
       , Ord (variable level)
       , Ord (variable Meta)
       , Ord (variable Object)
       , SortedVariable variable
       , Show (variable level)
       , Hashable variable
       , FreshVariable variable
       , MonadCounter m
       )
    => MetadataTools level StepperAttributes
    -> UnificationSubstitution level variable
    -> ExceptT
        UnificationError
        m
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
