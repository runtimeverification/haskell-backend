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

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( makeInPredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Function.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.OrOfExpandedPattern
                 ( MultiOr, OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( crossProductGeneric, flatten, isFalse, isTrue, make )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluate, simplifyEvaluated )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Unparser
import           Kore.Variables.Fresh

{-|'simplify' simplifies an 'In' pattern with 'OrOfExpandedPattern'
children.

Right now this uses the following simplifications:

* bottom in a = bottom
* a in bottom = bottom
* top in a = ceil(a)
* a in top = ceil(a)

TODO(virgil): It does not have yet a special case for children with top terms.
-}
simplify
    ::  ( MetaOrObject level
        , FreshVariable variable
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from symbol IDs to defined functions
    -> In level (OrOfExpandedPattern level variable)
    -> Simplifier
        ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
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

> CofreeF (In level) (Valid level) (OrOfExpandedPattern level variable)

instead of two 'OrOfExpandedPattern' arguments. The type of 'makeEvaluateIn' may
be changed analogously. The 'Valid' annotation will eventually cache information
besides the pattern sort, which will make it even more useful to carry around.

-}
simplifyEvaluatedIn
    :: forall level variable .
        ( MetaOrObject level
        , FreshVariable variable
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from symbol IDs to defined functions
    -> OrOfExpandedPattern level variable
    -> OrOfExpandedPattern level variable
    -> Simplifier
        (OrOfExpandedPattern level variable, SimplificationProof level)
simplifyEvaluatedIn
    tools substitutionSimplifier simplifier axiomIdToSimplifier first second
  | OrOfExpandedPattern.isFalse first =
    return (OrOfExpandedPattern.make [], SimplificationProof)
  | OrOfExpandedPattern.isFalse second =
    return (OrOfExpandedPattern.make [], SimplificationProof)

  | OrOfExpandedPattern.isTrue first =
    Ceil.simplifyEvaluated
        tools substitutionSimplifier simplifier axiomIdToSimplifier second
  | OrOfExpandedPattern.isTrue second =
    Ceil.simplifyEvaluated
        tools substitutionSimplifier simplifier axiomIdToSimplifier first

  | otherwise = do
    let
        crossProduct
            :: MultiOr
                (Simplifier
                    ( OrOfExpandedPattern level variable
                    , SimplificationProof level
                    )
                )
        crossProduct =
            OrOfExpandedPattern.crossProductGeneric
                (makeEvaluateIn
                    tools substitutionSimplifier simplifier axiomIdToSimplifier
                )
                first
                second
    orOfOrProof <- sequence crossProduct
    let
        orOfOr :: MultiOr (OrOfExpandedPattern level variable)
        orOfOr = fmap dropProof orOfOrProof
    -- TODO: It's not obvious at all when filtering occurs and when it doesn't.
    return (OrOfExpandedPattern.flatten orOfOr, SimplificationProof)
  where
    dropProof
        :: (OrOfExpandedPattern level variable, SimplificationProof level)
        -> OrOfExpandedPattern level variable
    dropProof = fst

    {-
    ( OrOfExpandedPattern.flatten
        -- TODO: Remove fst.
        (fst <$> OrOfExpandedPattern.crossProductGeneric
            (makeEvaluateIn tools substitutionSimplifier) first second
        )
    , SimplificationProof
    )
    -}

makeEvaluateIn
    ::  ( MetaOrObject level
        , FreshVariable variable
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from symbol IDs to defined functions
    -> ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> Simplifier
        (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateIn
    tools substitutionSimplifier simplifier axiomIdToSimplifier first second
  | ExpandedPattern.isTop first =
    Ceil.makeEvaluate
        tools substitutionSimplifier simplifier axiomIdToSimplifier second
  | ExpandedPattern.isTop second =
    Ceil.makeEvaluate
        tools substitutionSimplifier simplifier axiomIdToSimplifier first
  | ExpandedPattern.isBottom first || ExpandedPattern.isBottom second =
    return (OrOfExpandedPattern.make [], SimplificationProof)
  | otherwise = return $ makeEvaluateNonBoolIn first second

makeEvaluateNonBoolIn
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateNonBoolIn patt1 patt2 =
    ( OrOfExpandedPattern.make
        [ Predicated
            { term = mkTop_
            , predicate =
                makeInPredicate
                    -- TODO: Wrap in 'contained' and 'container'.
                    (ExpandedPattern.toMLPattern patt1)
                    (ExpandedPattern.toMLPattern patt2)
            , substitution = mempty
            }
        ]
    , SimplificationProof
    )
