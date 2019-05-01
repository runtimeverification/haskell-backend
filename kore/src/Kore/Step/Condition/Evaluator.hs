{-|
Module      : Kore.Step.Condition.Evaluator
Description : Evaluates conditions.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Condition.Evaluator
    ( evaluate
    ) where

import Data.Reflection

import           Kore.Attribute.Symbol
import           Kore.IndexedModule.MetadataTools
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.Pattern as Pattern
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier,
                 SimplificationProof (SimplificationProof), Simplifier,
                 TermLikeSimplifier, simplifyTerm )
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

{- | Attempt to evaluate a predicate.

If the predicate is non-trivial (not @\\top{_}()@ or @\\bottom{_}()@),
@evaluate@ attempts to refute the predicate using an external SMT solver.

 -}
evaluate
    ::  forall variable .
        ( FreshVariable variable
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , Given (SmtMetadataTools StepperAttributes)
        )
    => PredicateSimplifier Object
    -> TermLikeSimplifier Object
    -- ^ Evaluates functions in a pattern.
    -> Syntax.Predicate variable
    -- ^ The condition to be evaluated.
    -- TODO: Can't it happen that I also get a substitution when evaluating
    -- functions? See the Equals case.
    -> Simplifier
        (Predicate variable, SimplificationProof Object)
evaluate
    substitutionSimplifier
    termSimplifier
    predicate
  = do
    (simplified, _proof) <-
        simplifyTerm' (Syntax.Predicate.unwrapPredicate predicate)
    refute <-
        case () of
            _ | OrPattern.isTrue simplified  -> return (Just True)
              | OrPattern.isFalse simplified -> return (Just False)
              | otherwise -> SMT.Evaluator.decidePredicate predicate
    let simplified' =
            case refute of
                Just False -> Pattern.bottom
                Just True -> Pattern.top
                _ -> OrPattern.toExpandedPattern simplified
        (subst, _proof) = asPredicate simplified'
    return (subst, SimplificationProof)
  where
    simplifyTerm' = simplifyTerm termSimplifier substitutionSimplifier

asPredicate
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => Pattern variable
    -> (Predicate variable, SimplificationProof Object)
asPredicate
    Conditional {term, predicate, substitution}
  =
    let
        andPatt =
            Syntax.Predicate.makeAndPredicate predicate
            $ Syntax.Predicate.wrapPredicate term
    in
        ( Conditional
            { term = ()
            , predicate = andPatt
            , substitution = substitution
            }
        , SimplificationProof
        )
