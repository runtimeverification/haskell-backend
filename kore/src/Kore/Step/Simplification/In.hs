{-|
Module      : Kore.Step.Simplification.In
Description : Tools for In pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.In
    (simplify
    ) where

import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( makeInPredicate )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( crossProductGeneric )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluate, simplifyEvaluated )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, Simplifier, TermLikeSimplifier )
import           Kore.Syntax.In
import           Kore.Unparser
import           Kore.Variables.Fresh

{-|'simplify' simplifies an 'In' pattern with 'OrPattern'
children.

Right now this uses the following simplifications:

* bottom in a = bottom
* a in bottom = bottom
* top in a = ceil(a)
* a in top = ceil(a)

TODO(virgil): It does not have yet a special case for children with top terms.
-}
simplify
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> In Sort (OrPattern variable)
    -> Simplifier (OrPattern variable)
simplify
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    In
        { inContainedChild = first
        , inContainingChild = second
        }
  =
    simplifyEvaluatedIn
        tools substitutionSimplifier simplifier axiomIdToSimplifier first second

{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make
'simplifyEvaluatedIn' take an argument of type

> CofreeF (In Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of two 'OrPattern' arguments. The type of 'makeEvaluateIn' may
be changed analogously. The 'Attribute.Pattern' annotation will eventually cache information
besides the pattern sort, which will make it even more useful to carry around.

-}
simplifyEvaluatedIn
    :: forall variable .
        ( FreshVariable variable
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> OrPattern variable
    -> OrPattern variable
    -> Simplifier (OrPattern variable)
simplifyEvaluatedIn
    tools substitutionSimplifier simplifier axiomIdToSimplifier first second
  | OrPattern.isFalse first  = return OrPattern.bottom
  | OrPattern.isFalse second = return OrPattern.bottom

  | OrPattern.isTrue first =
    Ceil.simplifyEvaluated
        tools substitutionSimplifier simplifier axiomIdToSimplifier second
  | OrPattern.isTrue second =
    Ceil.simplifyEvaluated
        tools substitutionSimplifier simplifier axiomIdToSimplifier first

  | otherwise = do
    let
        crossProduct =
            MultiOr.crossProductGeneric
                (makeEvaluateIn
                    tools substitutionSimplifier simplifier axiomIdToSimplifier
                )
                first
                second
    OrPattern.flatten <$> sequence crossProduct

makeEvaluateIn
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> Pattern variable
    -> Pattern variable
    -> Simplifier (OrPattern variable)
makeEvaluateIn
    tools substitutionSimplifier simplifier axiomIdToSimplifier first second
  | Pattern.isTop first =
    Ceil.makeEvaluate
        tools substitutionSimplifier simplifier axiomIdToSimplifier second
  | Pattern.isTop second =
    Ceil.makeEvaluate
        tools substitutionSimplifier simplifier axiomIdToSimplifier first
  | Pattern.isBottom first || Pattern.isBottom second =
    return OrPattern.bottom
  | otherwise = return $ makeEvaluateNonBoolIn first second

makeEvaluateNonBoolIn
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => Pattern variable
    -> Pattern variable
    -> OrPattern variable
makeEvaluateNonBoolIn patt1 patt2 =
    OrPattern.fromPattern Conditional
        { term = mkTop_
        , predicate =
            makeInPredicate
                -- TODO: Wrap in 'contained' and 'container'.
                (Pattern.toMLPattern patt1)
                (Pattern.toMLPattern patt2)
        , substitution = mempty
        }
