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

import           Kore.AST.Common
                 ( SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.AST.Valid
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Merging.OrOfExpandedPattern as OrOfExpandedPattern
                 ( mergeWithPredicateSubstitutionAssumesEvaluated )
import           Kore.Step.Pattern
import           Kore.Step.Representation.ExpandedPattern
                 ( Predicated (..) )
import qualified Kore.Step.Representation.ExpandedPattern as Predicated
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make )
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfPredicateSubstitution )
import           Kore.Step.Simplification.AndTerms
                 ( termUnification )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluateTerm )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, StepPatternSimplifier )
import           Kore.Step.Substitution
                 ( createPredicatesAndSubstitutionsMerger )
import           Kore.Unification.Data
                 ( UnificationProof (..) )
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
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , MetaOrObject level
        , FreshVariable variable
        , MonadUnify unifierM
        , unifier ~ unifierM variable
        )
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from symbol IDs to defined functions
    -> StepPattern level variable
    -- ^left-hand-side of unification
    -> StepPattern level variable
    -> unifier
        ( OrOfPredicateSubstitution level variable
        , UnificationProof level variable
        )
unificationProcedure
    tools substitutionSimplifier simplifier axiomIdToSimplifier p1 p2
  | p1Sort /= p2Sort =
    return (MultiOr.make [], EmptyUnificationProof)
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
    (pat@Predicated { term, predicate, substitution }, _) <- getUnifiedTerm
    if Predicated.isBottom pat
        then return
            (MultiOr.make [], EmptyUnificationProof)
        else Monad.Unify.liftSimplifier $ do
            (orCeil, _proof) <-
                Ceil.makeEvaluateTerm
                    tools
                    substitutionSimplifier
                    simplifier
                    axiomIdToSimplifier
                    term
            (result, _proof) <-
                OrOfExpandedPattern.mergeWithPredicateSubstitutionAssumesEvaluated
                    (createPredicatesAndSubstitutionsMerger
                        tools
                        substitutionSimplifier
                        simplifier
                        axiomIdToSimplifier
                    )
                    Predicated
                        { term = ()
                        , predicate
                        , substitution
                        }
                    orCeil
            return (result, EmptyUnificationProof)
  where
      p1Sort = getSort p1
      p2Sort = getSort p2
