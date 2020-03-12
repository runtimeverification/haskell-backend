{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.Condition
    ( create
    , simplify
    , simplifyPredicate
    , simplifyCondition
    ) where

import Prelude.Kore

import qualified Data.Text.Prettyprint.Doc as Pretty

import Branch
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.Pattern
    ( Condition
    , Conditional (..)
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    , unwrapPredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Step.Simplification.Simplify
import Kore.Step.Simplification.SubstitutionSimplifier
    ( SubstitutionSimplifier (..)
    )
import qualified Kore.TopBottom as TopBottom
import Kore.Unparser

{- | Create a 'ConditionSimplifier' using 'simplify'.
-}
create
    :: MonadSimplify simplifier
    => SubstitutionSimplifier simplifier
    -> ConditionSimplifier simplifier
create substitutionSimplifier =
    ConditionSimplifier $ simplify substitutionSimplifier

{- | Simplify a 'Condition'.

@simplify@ applies the substitution to the predicate and simplifies the
result. The result is re-simplified until it stabilizes.

The 'term' of 'Conditional' may be any type; it passes through @simplify@
unmodified.
-}
simplify
    ::  forall simplifier variable any
    .   ( HasCallStack
        , InternalVariable variable
        , MonadSimplify simplifier
        )
    =>  SubstitutionSimplifier simplifier
    ->  SideCondition variable
    ->  Conditional variable any
    ->  BranchT simplifier (Conditional variable any)
simplify SubstitutionSimplifier { simplifySubstitution } sideCondition initial =
    normalize initial >>= worker
  where
    worker Conditional { term, predicate, substitution } = do
        let substitution' = Substitution.toMap substitution
            predicate' = Predicate.substitute substitution' predicate
        simplified <- simplifyPredicate sideCondition predicate'
        TopBottom.guardAgainstBottom simplified
        let merged = simplified <> Condition.fromSubstitution substitution
        normalized <- normalize merged
        -- Check for full simplification *after* normalization. Simplification
        -- may have produced irrelevant substitutions that become relevant after
        -- normalization.
        if fullySimplified normalized
            then return normalized { term }
            else worker normalized { term }

    fullySimplified Conditional { predicate, substitution } =
        Predicate.isFreeOf predicate variables
      where
        variables = Substitution.variables substitution

    normalize
        ::  forall any'
        .   Conditional variable any'
        ->  BranchT simplifier (Conditional variable any')
    normalize conditional@Conditional { substitution } = do
        let conditional' = conditional { substitution = mempty }
        predicates' <- lift $
            simplifySubstitution sideCondition substitution
        predicate' <- Branch.scatter predicates'
        return $ Conditional.andCondition conditional' predicate'

{- | Simplify the 'Predicate' once.

@simplifyPredicate@ does not attempt to apply the resulting substitution and
re-simplify the result.

See also: 'simplify'

-}
simplifyPredicate
    ::  ( HasCallStack
        , InternalVariable variable
        , MonadSimplify simplifier
        )
    =>  SideCondition variable
    ->  Predicate variable
    ->  BranchT simplifier (Condition variable)
simplifyPredicate sideCondition predicate = do
    patternOr <-
        lift
        $ simplifyConditionalTermToOr sideCondition
        $ unwrapPredicate predicate
    -- Despite using lift above, we do not need to
    -- explicitly check for \bottom because patternOr is an OrPattern.
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
