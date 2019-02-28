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

import Data.List
       ( group )

import           Kore.AST.Common
                 ( SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.ExpandedPattern
                 ( PredicateSubstitution, Predicated (..) )
import           Kore.Step.Function.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier (..),
                 SimplificationProof (..), Simplifier, StepPatternSimplifier )
import qualified Kore.Step.Simplification.Predicate as Predicate
                 ( simplifyPartial )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
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
        (\p -> simplify tools simplifier axiomIdToSimplifier p 0)

{-| Simplifies a predicate-substitution by applying the substitution to the
predicate, simplifying the result and repeating with the new
substitution-predicate.
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
    -> PredicateSubstitution level variable
    -> Int
    -> Simplifier
        ( PredicateSubstitution level variable
        , SimplificationProof level
        )
simplify
    tools
    simplifier
    axiomIdToSimplifier
    initialValue@Predicated { predicate, substitution }
    times
  = do
    let substitution' = Substitution.toMap substitution
        substitutedPredicate = Predicate.substitute substitution' predicate
    -- TODO(Vladimir): This is an ugly hack that fixes EVM execution. Should
    -- probably be fixed in 'Kore.Step.Simplification.Pattern'.
    -- This was needed because, when we need to simplify 'requires' clauses,
    -- this needs to run more than once.
    if substitutedPredicate == predicate && times > 1
        then return (initialValue, SimplificationProof)
        else do
            (   Predicated
                    { predicate = simplifiedPredicate
                    , substitution = simplifiedSubstitution
                    }
                , _proof
                ) <-
                    Predicate.simplifyPartial
                        substitutionSimplifier
                        simplifier
                        substitutedPredicate

            if Substitution.null simplifiedSubstitution
                then return
                    ( Predicated
                        { term = ()
                        , predicate = simplifiedPredicate
                        , substitution
                        }
                    , SimplificationProof
                    )
                else do
                    -- TODO(virgil): Optimize. Since both substitution and
                    -- simplifiedSubstitution have distinct variables, it is
                    -- enough to check that, say, simplifiedSubstitution's
                    -- variables are not among substitution's variables.
                    assertDistinctVariables
                        (substitution <> simplifiedSubstitution)
                    (mergedPredicateSubstitution, _proof) <-
                        mergePredicatesAndSubstitutions
                            tools
                            substitutionSimplifier
                            simplifier
                            axiomIdToSimplifier
                            [simplifiedPredicate]
                            [substitution, simplifiedSubstitution]
                    return (mergedPredicateSubstitution, SimplificationProof)
  where
    substitutionSimplifier =
        PredicateSubstitutionSimplifier
            (\p -> simplify tools simplifier axiomIdToSimplifier p (times + 1))

assertDistinctVariables
    :: forall level variable
    .   ( Show (variable level)
        , Eq (variable level)
        )
    => Substitution level variable
    -> Simplifier ()
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
