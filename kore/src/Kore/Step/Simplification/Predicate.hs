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
import qualified GHC.Stack as GHC

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
import Kore.Step.Substitution
    ( normalize
    )
import qualified Kore.TopBottom as TopBottom
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unparser

{- | Create a 'PredicateSimplifier' using 'simplify'.
-}
create :: MonadSimplify simplifier => PredicateSimplifier simplifier
create = PredicateSimplifier simplify

{- | Simplify a 'Predicate'.

@simplify@ applies the substitution to the predicate and simplifies the
result. The result is re-simplified until it stabilizes.

The 'term' of 'Conditional' may be any type; it passes through @simplify@
unmodified.

-}
simplify
    ::  forall simplifier variable any
    .   ( GHC.HasCallStack
        , SimplifierVariable variable
        , MonadSimplify simplifier
        )
    =>  Conditional variable any
    ->  BranchT simplifier (Conditional variable any)
simplify initial = normalize initial >>= worker
  where
    worker Conditional { term, predicate, substitution } = do
        let substitution' = Substitution.toMap substitution
            predicate' = Syntax.Predicate.substitute substitution' predicate
        simplified <- simplifyPartial predicate'
        TopBottom.guardAgainstBottom simplified
        let merged = simplified <> Predicate.fromSubstitution substitution
        normalized <- normalize merged
        if fullySimplified normalized
            then return normalized { term }
            else worker normalized { term }

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
    ::  ( GHC.HasCallStack
        , SimplifierVariable variable
        , MonadSimplify simplifier
        )
    =>  Syntax.Predicate variable
    ->  BranchT simplifier (Predicate variable)
simplifyPartial predicate = do
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
