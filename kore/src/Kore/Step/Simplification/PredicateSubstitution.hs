{-|
Module      : Kore.Step.Simplification.PredicateSubstitution
Description : Tools for PredicateSubstitution simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.PredicateSubstitution
    ( create
    , simplify
    ) where

import qualified Control.Monad.Trans as Monad.Trans
import           Data.List
                 ( group )

import           Kore.AST.Common
                 ( SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Representation.ExpandedPattern
                 ( PredicateSubstitution, Predicated (..) )
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Predicate as Predicate
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import qualified Kore.TopBottom as TopBottom
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

{-| Creates a predicate simplifier, see `simplify` below.
-}
create
    :: MetadataTools level StepperAttributes
    -> StepPatternSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -> PredicateSubstitutionSimplifier level
create tools simplifier axiomIdToSimplifier =
    PredicateSubstitutionSimplifier
        (simplify tools simplifier axiomIdToSimplifier 0)

{- | Simplify a 'PredicateSubstitution'.

@simplify@ applies the substitution to the predicate and simplifies the
result. The result is re-simplified once.

-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        )
    => MetadataTools level StepperAttributes
    -> StepPatternSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> Int
    -> PredicateSubstitution level variable
    -> BranchT Simplifier (PredicateSubstitution level variable)
simplify
    tools
    simplifier
    axiomIdToSimplifier
    times
    initialValue@Predicated { predicate, substitution }
  = do
    let substitution' = Substitution.toMap substitution
        substitutedPredicate = Predicate.substitute substitution' predicate
    -- TODO(Vladimir): This is an ugly hack that fixes EVM execution. Should
    -- probably be fixed in 'Kore.Step.Simplification.Pattern'.
    -- This was needed because, when we need to simplify 'requires' clauses,
    -- this needs to run more than once.
    if substitutedPredicate == predicate && times > 1
        then return initialValue
        else do
            simplified <-
                Predicate.simplifyPartial
                    substitutionSimplifier
                    simplifier
                    substitutedPredicate

            let Predicated { predicate = simplifiedPredicate } = simplified
                Predicated { substitution = simplifiedSubstitution } =
                    simplified

            if Substitution.null simplifiedSubstitution
                then return simplified { substitution }
                else do
                    -- TODO(virgil): Optimize. Since both substitution and
                    -- simplifiedSubstitution have distinct variables, it is
                    -- enough to check that, say, simplifiedSubstitution's
                    -- variables are not among substitution's variables.
                    assertDistinctVariables
                        (substitution <> simplifiedSubstitution)
                    (mergedPredicateSubstitution, _proof) <-
                        Monad.Trans.lift
                        $ mergePredicatesAndSubstitutions
                            tools
                            substitutionSimplifier
                            simplifier
                            axiomIdToSimplifier
                            [simplifiedPredicate]
                            [substitution, simplifiedSubstitution]
                    TopBottom.guardAgainstBottom mergedPredicateSubstitution
                    return mergedPredicateSubstitution
  where
    substitutionSimplifier =
        PredicateSubstitutionSimplifier
            (simplify tools simplifier axiomIdToSimplifier (times + 1))

assertDistinctVariables
    :: forall level variable m
    .   ( Show (variable level)
        , Eq (variable level)
        , Monad m
        )
    => Substitution level variable
    -> m ()
assertDistinctVariables subst =
    case filter moreThanOne (group variables) of
        [] -> return ()
        (var : _) -> error ("Duplicated variable: " ++ show var)
  where
    moreThanOne :: [variable level] -> Bool
    moreThanOne [] = False
    moreThanOne [_] = False
    moreThanOne _ = True

    variables :: [variable level]
    variables = Substitution.variables subst
