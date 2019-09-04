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
import qualified Data.Foldable as Foldable
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty

import qualified Kore.Internal.Conditional as Conditional
import           Kore.Internal.Pattern
                 ( Conditional (..), Predicate )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate, unwrapPredicate )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
                 ( substitute )
import           Kore.Step.Simplification.Data
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import qualified Kore.TopBottom as TopBottom
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser

{- | Create a 'PredicateSimplifier' using 'simplify'.
-}
create :: PredicateSimplifier
create = PredicateSimplifier (simplify 0)

{- | Simplify a 'Predicate'.

@simplify@ applies the substitution to the predicate and simplifies the
result. The result is re-simplified once.

-}
simplify
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => Int
    -> Predicate variable
    -> BranchT simplifier (Predicate variable)
simplify
    times
    initialValue@Conditional { predicate, substitution }
  = do
    let substitution' = Substitution.toMap substitution
        substitutedPredicate =
            Syntax.Predicate.substitute substitution' predicate
    -- TODO(Vladimir): This is an ugly hack that fixes EVM execution. Should
    -- probably be fixed in 'Kore.Step.Simplification.Pattern'.
    -- This was needed because, when we need to simplify 'requires' clauses,
    -- this needs to run more than once.
    if substitutedPredicate == predicate && times > 1
        then return initialValue
        else localPredicateSimplifier $ do
            simplified <- simplifyPartial substitutedPredicate

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
                    assertDistinctVariables substitution simplifiedSubstitution
                    mergedPredicate <-
                        mergePredicatesAndSubstitutions
                            [simplifiedPredicate]
                            [substitution, simplifiedSubstitution]
                    TopBottom.guardAgainstBottom mergedPredicate
                    return mergedPredicate
  where
    substitutionSimplifier = PredicateSimplifier (simplify (times + 1))
    localPredicateSimplifier =
        localSimplifierPredicate (const substitutionSimplifier)

assertDistinctVariables
    :: forall variable m
    .   ( Ord variable
        , Unparse variable
        , Monad m
        )
    => Substitution variable
    -> Substitution variable
    -> m ()
assertDistinctVariables subst1 subst2
  | null intersection = return ()
  | otherwise =
    (error . show . Pretty.vsep)
        [ "Duplicated variables:"
        , Pretty.indent 4 . Pretty.vsep $ unparse <$> intersection
        ]
  where
    intersection = Foldable.toList $ Set.intersection vars1 vars2
    vars1 = Substitution.variables subst1
    vars2 = Substitution.variables subst2

{- | Simplify the 'Syntax.Predicate' once; do not apply the substitution.

@simplifyPartial@ does not attempt to apply the resulting substitution and
re-simplify the result.

See also: 'simplify'

-}
simplifyPartial
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => Syntax.Predicate variable
    -> BranchT simplifier (Predicate variable)
simplifyPartial
    predicate
  = do
    patternOr <-
        Monad.Trans.lift $ simplifyTerm $ Syntax.unwrapPredicate predicate
    -- Despite using Monad.Trans.lift above, we do not need to explicitly check
    -- for \bottom because patternOr is an OrPattern.
    scatter (eraseTerm <$> patternOr)
  where
    eraseTerm conditional
      | TopBottom.isTop (Pattern.term conditional)
      = Conditional.withoutTerm conditional
      | otherwise =
        (error . show . Pretty.vsep)
            [ "Expecting a \\top term, but found:"
            , unparse conditional
            ]
