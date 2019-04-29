{-|
Module      : Kore.Step.Simplification.Predicate
Description : Predicate simplification.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Predicate
    ( create
    , simplify
    , simplifyPartial
    ) where

import qualified Control.Monad.Trans as Monad.Trans
import           Data.List
                 ( group )
import qualified Data.Text.Prettyprint.Doc as Pretty

import           Kore.AST.MetaOrObject
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate, unwrapPredicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Pattern
                 ( Conditional (..), Predicate )
import           Kore.Step.Simplification.Data
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Syntax.Variable
                 ( SortedVariable )
import qualified Kore.TopBottom as TopBottom
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

{- | Create a 'PredicateSimplifier' using 'simplify'.
-}
create
    :: SmtMetadataTools StepperAttributes
    -> TermLikeSimplifier Object
    -> BuiltinAndAxiomSimplifierMap Object
    -> PredicateSimplifier Object
create tools simplifier axiomIdToSimplifier =
    PredicateSimplifier
        (simplify tools simplifier axiomIdToSimplifier 0)

{- | Simplify a 'Predicate'.

@simplify@ applies the substitution to the predicate and simplifies the
result. The result is re-simplified once.

-}
simplify
    ::  ( MetaOrObject Object
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> TermLikeSimplifier Object
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from axiom IDs to axiom evaluators
    -> Int
    -> Predicate Object variable
    -> BranchT Simplifier (Predicate Object variable)
simplify
    tools
    simplifier
    axiomIdToSimplifier
    times
    initialValue@Conditional { predicate, substitution }
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
                simplifyPartial
                    substitutionSimplifier
                    simplifier
                    substitutedPredicate

            let Conditional { predicate = simplifiedPredicate } = simplified
                Conditional { substitution = simplifiedSubstitution } =
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
                    (mergedPredicate, _proof) <-
                        Monad.Trans.lift
                        $ mergePredicatesAndSubstitutions
                            tools
                            substitutionSimplifier
                            simplifier
                            axiomIdToSimplifier
                            [simplifiedPredicate]
                            [substitution, simplifiedSubstitution]
                    TopBottom.guardAgainstBottom mergedPredicate
                    return mergedPredicate
  where
    substitutionSimplifier =
        PredicateSimplifier
            (simplify tools simplifier axiomIdToSimplifier (times + 1))

assertDistinctVariables
    :: forall variable m
    .   ( Show variable
        , Eq variable
        , Monad m
        )
    => Substitution variable
    -> m ()
assertDistinctVariables subst =
    case filter moreThanOne (group variables) of
        [] -> return ()
        (var : _) -> error ("Duplicated variable: " ++ show var)
  where
    moreThanOne :: [variable] -> Bool
    moreThanOne [] = False
    moreThanOne [_] = False
    moreThanOne _ = True

    variables :: [variable]
    variables = Substitution.variables subst

{- | Simplify the 'Syntax.Predicate' once; do not apply the substitution.

@simplifyPartial@ does not attempt to apply the resulting substitution and
re-simplify the result.

See also: 'simplify'

-}
simplifyPartial
    ::  ( FreshVariable variable
        , MetaOrObject level
        , Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        )
    => PredicateSimplifier level
    -> TermLikeSimplifier level
    -> Syntax.Predicate variable
    -> BranchT Simplifier (Predicate level variable)
simplifyPartial
    substitutionSimplifier
    termSimplifier
    predicate
  = do
    (patternOr, _proof) <-
        Monad.Trans.lift
        $ simplifyTerm'
        $ Syntax.unwrapPredicate predicate
    -- Despite using Monad.Trans.lift above, we do not need to explicitly check
    -- for \bottom because patternOr is an OrPattern.
    scatter (eraseTerm <$> patternOr)
  where
    simplifyTerm' = simplifyTerm termSimplifier substitutionSimplifier
    eraseTerm conditional@Conditional { term }
      | TopBottom.isTop term = conditional { term = () }
      | otherwise =
        (error . show . Pretty.vsep)
            [ "Expecting a \\top term, but found:"
            , unparse conditional
            ]
