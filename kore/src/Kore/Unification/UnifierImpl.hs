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

import qualified Control.Comonad.Trans.Cofree as Cofree
import           Control.Monad
                 ( foldM )
import           Data.Function
                 ( on )
import qualified Data.Functor.Foldable as Recursive
import           Data.List
                 ( foldl', groupBy, partition, sortBy )
import           Data.List.NonEmpty
                 ( NonEmpty (..) )

import           Kore.Attribute.Symbol
import           Kore.IndexedModule.MetadataTools
import qualified Kore.Predicate.Predicate as Predicate
                 ( isFalse, makeAndPredicate )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Conditional as Conditional
import           Kore.Step.Pattern as Pattern
import           Kore.Step.Predicate
                 ( Conditional (..), Predicate )
import qualified Kore.Step.Predicate as Predicate
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier (..), TermLikeSimplifier )
import           Kore.Step.TermLike
                 ( TermLike )
import           Kore.Syntax.And
import qualified Kore.Syntax.PatternF as Syntax
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unification.Unify
                 ( MonadUnify )
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

import {-# SOURCE #-} Kore.Step.Simplification.AndTerms
       ( termUnification )
import {-# SOURCE #-} Kore.Step.Substitution
       ( mergePredicatesAndSubstitutionsExcept )

simplifyAnds
    ::  forall variable unifier unifierM .
        ( Show variable
        , Unparse variable
        , SortedVariable variable
        , FreshVariable variable
        , unifier ~ unifierM variable
        , MonadUnify unifierM
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -> NonEmpty (TermLike variable)
    -> unifier (Pattern variable)
simplifyAnds
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    patterns
  = do
    result <- foldM simplifyAnds' Pattern.top patterns
    if Predicate.isFalse . Pattern.predicate $ result
        then return Pattern.bottom
        else return result
  where
    simplifyAnds'
        :: Pattern variable
        -> TermLike variable
        -> unifier (Pattern variable)
    simplifyAnds' intermediate pat =
        case Cofree.tailF (Recursive.project pat) of
            Syntax.AndF And { andFirst = lhs, andSecond = rhs } ->
                foldM simplifyAnds' intermediate [lhs, rhs]
            _ -> do
                result <-
                    termUnification
                        tools
                        substitutionSimplifier
                        simplifier
                        axiomIdToSimplifier
                        (Pattern.term intermediate)
                        pat
                predSubst <-
                    mergePredicatesAndSubstitutionsExcept
                        tools
                        substitutionSimplifier
                        simplifier
                        axiomIdToSimplifier
                        [ Pattern.predicate result
                        , Pattern.predicate intermediate
                        ]
                        [ Pattern.substitution result
                        , Pattern.substitution intermediate
                        ]
                return Pattern.Conditional
                    { term = Pattern.term result
                    , predicate = Conditional.predicate predSubst
                    , substitution = Conditional.substitution predSubst
                    }


groupSubstitutionByVariable
    :: Ord variable
    => [(variable, TermLike variable)]
    -> [[(variable, TermLike variable)]]
groupSubstitutionByVariable =
    groupBy ((==) `on` fst) . sortBy (compare `on` fst) . map sortRenaming
  where
    sortRenaming (var, Recursive.project -> ann :< Syntax.VariableF var')
        | var' < var =
          (var', Recursive.embed (ann :< Syntax.VariableF var))
    sortRenaming eq = eq

-- simplifies x = t1 /\ x = t2 /\ ... /\ x = tn by transforming it into
-- x = ((t1 /\ t2) /\ (..)) /\ tn
-- then recursively reducing that to finally get x = t /\ subst
solveGroupedSubstitution
    :: ( Show variable
       , Unparse variable
       , SortedVariable variable
       , FreshVariable variable
       , MonadUnify unifierM
       , unifier ~ unifierM variable
      )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -> variable
    -> NonEmpty (TermLike variable)
    -> unifier
        ( Predicate variable

        )
solveGroupedSubstitution
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    var
    patterns
  = do
    predSubst <-
        simplifyAnds
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            patterns
    return Conditional
        { term = ()
        , predicate = Pattern.predicate predSubst
        , substitution = Substitution.wrap $ termAndSubstitution predSubst
        }
  where
    termAndSubstitution s =
        (var, Pattern.term s)
        : Substitution.unwrap (Pattern.substitution s)

-- |Takes a potentially non-normalized substitution,
-- and if it contains multiple assignments to the same variable,
-- it solves all such assignments.
-- As new assignments may be produced during the solving process,
-- `normalizeSubstitutionDuplication` recursively calls itself until it
-- stabilizes.
normalizeSubstitutionDuplication
    :: forall variable unifier unifierM
    .   ( Show variable
        , Unparse variable
        , SortedVariable variable
        , FreshVariable variable
        , MonadUnify unifierM
        , unifier ~ unifierM variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -> Substitution variable
    -> unifier
        ( Predicate variable

        )
normalizeSubstitutionDuplication
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    subst
  =
    if null nonSingletonSubstitutions || Substitution.isNormalized subst
        then return $ Predicate.fromSubstitution subst
        else do
            predSubst <-
                mergePredicateList
                <$> mapM
                    (uncurry
                        $ solveGroupedSubstitution
                            tools
                            substitutionSimplifier
                            simplifier
                            axiomIdToSimplifier
                    )
                    varAndSubstList
            finalSubst <-
                normalizeSubstitutionDuplication
                    tools
                    substitutionSimplifier
                    simplifier
                    axiomIdToSimplifier
                    (  Substitution.wrap (concat singletonSubstitutions)
                    <> Conditional.substitution predSubst
                    )
            let
                pred' =
                    Predicate.makeAndPredicate
                        (Conditional.predicate predSubst)
                        (Conditional.predicate finalSubst)
            return Conditional
                { term = ()
                , predicate = pred'
                , substitution = Conditional.substitution finalSubst
                }
  where
    groupedSubstitution = groupSubstitutionByVariable $ Substitution.unwrap subst
    isSingleton [_] = True
    isSingleton _   = False
    singletonSubstitutions, nonSingletonSubstitutions
        :: [[(variable, TermLike variable)]]
    (singletonSubstitutions, nonSingletonSubstitutions) =
        partition isSingleton groupedSubstitution
    varAndSubstList :: [(variable, NonEmpty (TermLike variable))]
    varAndSubstList =
        nonSingletonSubstitutions >>= \case
            [] -> []
            ((x, y) : ys) -> [(x, y :| (snd <$> ys))]


mergePredicateList
    :: ( Ord variable
       , Show variable
       , Unparse variable
       , SortedVariable variable
       )
    => [(Predicate variable)]
    -> (Predicate variable)
mergePredicateList [] = Predicate.top
mergePredicateList (p:ps) = foldl' (<>) p ps
