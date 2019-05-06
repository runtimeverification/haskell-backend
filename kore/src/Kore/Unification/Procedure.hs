{-|
Module      : Kore.Unification.Procedure
Description : Unification procedure.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Unification.Procedure
    ( unificationProcedure
    ) where

import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.OrPredicate
                 ( OrPredicate )
import qualified Kore.Internal.OrPredicate as OrPredicate
import           Kore.Internal.Pattern
                 ( Conditional (..) )
import qualified Kore.Internal.Pattern as Conditional
import           Kore.Internal.TermLike
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Merging.OrPattern as OrPattern
import           Kore.Step.Simplification.AndTerms
                 ( termUnification )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluateTerm )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, TermLikeSimplifier )
import           Kore.Step.Substitution
                 ( createPredicatesAndSubstitutionsMerger )
import           Kore.Syntax.Variable
                 ( SortedVariable )
import           Kore.Unification.Unify
                 ( MonadUnify )
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )


-- |'unificationProcedure' atempts to simplify @t1 = t2@, assuming @t1@ and @t2@
-- are terms (functional patterns) to a substitution.
-- If successful, it also produces a proof of how the substitution was obtained.
-- If failing, it gives a 'UnificationError' reason for the failure.
unificationProcedure
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , MonadUnify unifierM
        , unifier ~ unifierM variable
        )
    => SmtMetadataTools StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> TermLike variable
    -- ^left-hand-side of unification
    -> TermLike variable
    -> unifier (OrPredicate variable)
unificationProcedure
    tools substitutionSimplifier simplifier axiomIdToSimplifier p1 p2
  | p1Sort /= p2Sort = return OrPredicate.bottom
  | otherwise = do
    let
        getUnifiedTerm =
            termUnification
                tools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                p1
                p2
    pat@Conditional { term, predicate, substitution } <- getUnifiedTerm
    if Conditional.isBottom pat
        then return OrPredicate.bottom
        else Monad.Unify.liftSimplifier $ do
            orCeil <-
                Ceil.makeEvaluateTerm
                    tools
                    substitutionSimplifier
                    simplifier
                    axiomIdToSimplifier
                    term
            OrPattern.mergeWithPredicateAssumesEvaluated
                (createPredicatesAndSubstitutionsMerger
                    tools
                    substitutionSimplifier
                    simplifier
                    axiomIdToSimplifier
                )
                Conditional
                    { term = ()
                    , predicate
                    , substitution
                    }
                orCeil
  where
      p1Sort = termLikeSort p1
      p2Sort = termLikeSort p2
