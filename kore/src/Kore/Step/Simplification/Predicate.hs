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
    , simplifyPredicate
    ) where

import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Text.Prettyprint.Doc as Pretty

import Branch
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.Pattern
    ( Conditional (..)
    , Predicate
    )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    , unwrapPredicate
    )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import Kore.Step.Simplification.Simplify
import qualified Kore.TopBottom as TopBottom
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unification.UnifierImpl as Unification
import Kore.Unification.Unify as Unifier
import Kore.Unparser

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
simplify times0 initial = normalize initial >>= worker times0
  where
    worker times Conditional { term = (), predicate, substitution } = do
        let substitution' = Substitution.toMap substitution
            predicate' = Syntax.Predicate.substitute substitution' predicate
        simplified <- simplifyPartial predicate'
        TopBottom.guardAgainstBottom simplified
        let merged = simplified <> Predicate.fromSubstitution substitution
        normalized <- normalize merged
        if fullySimplified normalized
            then return normalized
            else worker (times + 1) normalized

    fullySimplified Conditional { predicate, substitution } =
        Syntax.Predicate.isFreeOf predicate variables
      where
        variables = Substitution.variables substitution

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
    Branch.scatter (eraseTerm <$> patternOr)
  where
    eraseTerm conditional
      | TopBottom.isTop (Pattern.term conditional)
      = Conditional.withoutTerm conditional
      | otherwise =
        (error . show . Pretty.vsep)
            [ "Expecting a \\top term, but found:"
            , unparse conditional
            ]

-- | Normalize the substitution.
normalize
    :: forall variable term simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => Conditional variable term
    -> BranchT simplifier (Conditional variable term)
normalize Conditional { term, predicate, substitution } = do
    -- We collect all the results here because we should promote the
    -- substitution to the predicate when there is an error on *any* branch.
    results <-
        Monad.Trans.lift
        $ Unifier.runUnifierT
        $ Unification.normalizeOnce
            Conditional { term = (), predicate, substitution }
    case results of
        Right normal -> Branch.scatter (applyTerm <$> normal)
        Left _ ->
            return Conditional
                { term
                , predicate =
                    Syntax.Predicate.makeAndPredicate predicate
                    $ Syntax.Predicate.fromSubstitution substitution
                , substitution = mempty
                }
  where
    applyTerm predicated = predicated { term }
