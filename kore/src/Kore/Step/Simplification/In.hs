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

import           Kore.AST.Common
                 ( In (..) )
import           Kore.AST.Valid
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Predicate.Predicate
                 ( makeInPredicate )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Pattern as Pattern
import qualified Kore.Step.Pattern.Or as Or
import           Kore.Step.Representation.MultiOr
                 ( MultiOr )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( crossProductGeneric, flatten, make )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluate, simplifyEvaluated )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, SimplificationProof (..), Simplifier,
                 StepPatternSimplifier )
import           Kore.Unparser
import           Kore.Variables.Fresh

{-|'simplify' simplifies an 'In' pattern with 'Or.Pattern'
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
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier Object
    -> StepPatternSimplifier Object
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from symbol IDs to defined functions
    -> In Object (Or.Pattern Object variable)
    -> Simplifier
        ( Or.Pattern Object variable
        , SimplificationProof Object
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

> CofreeF (In Object) (Valid Object) (Or.Pattern Object variable)

instead of two 'Or.Pattern' arguments. The type of 'makeEvaluateIn' may
be changed analogously. The 'Valid' annotation will eventually cache information
besides the pattern sort, which will make it even more useful to carry around.

-}
simplifyEvaluatedIn
    :: forall variable .
        ( FreshVariable variable
        , SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier Object
    -> StepPatternSimplifier Object
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from symbol IDs to defined functions
    -> Or.Pattern Object variable
    -> Or.Pattern Object variable
    -> Simplifier
        (Or.Pattern Object variable, SimplificationProof Object)
simplifyEvaluatedIn
    tools substitutionSimplifier simplifier axiomIdToSimplifier first second
  | Or.isFalse first =
    return (MultiOr.make [], SimplificationProof)
  | Or.isFalse second =
    return (MultiOr.make [], SimplificationProof)

  | Or.isTrue first =
    Ceil.simplifyEvaluated
        tools substitutionSimplifier simplifier axiomIdToSimplifier second
  | Or.isTrue second =
    Ceil.simplifyEvaluated
        tools substitutionSimplifier simplifier axiomIdToSimplifier first

  | otherwise = do
    let
        crossProduct
            :: MultiOr
                (Simplifier
                    ( Or.Pattern Object variable
                    , SimplificationProof Object
                    )
                )
        crossProduct =
            MultiOr.crossProductGeneric
                (makeEvaluateIn
                    tools substitutionSimplifier simplifier axiomIdToSimplifier
                )
                first
                second
    orOfOrProof <- sequence crossProduct
    let
        orOfOr :: MultiOr (Or.Pattern Object variable)
        orOfOr = fmap dropProof orOfOrProof
    -- TODO: It's not obvious at all when filtering occurs and when it doesn't.
    return (MultiOr.flatten orOfOr, SimplificationProof)
  where
    dropProof
        :: (Or.Pattern Object variable, SimplificationProof Object)
        -> Or.Pattern Object variable
    dropProof = fst

    {-
    ( MultiOr.flatten
        -- TODO: Remove fst.
        (fst <$> MultiOr.crossProductGeneric
            (makeEvaluateIn tools substitutionSimplifier) first second
        )
    , SimplificationProof
    )
    -}

makeEvaluateIn
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier Object
    -> StepPatternSimplifier Object
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from symbol IDs to defined functions
    -> Pattern Object variable
    -> Pattern Object variable
    -> Simplifier
        (Or.Pattern Object variable, SimplificationProof Object)
makeEvaluateIn
    tools substitutionSimplifier simplifier axiomIdToSimplifier first second
  | Pattern.isTop first =
    Ceil.makeEvaluate
        tools substitutionSimplifier simplifier axiomIdToSimplifier second
  | Pattern.isTop second =
    Ceil.makeEvaluate
        tools substitutionSimplifier simplifier axiomIdToSimplifier first
  | Pattern.isBottom first || Pattern.isBottom second =
    return (MultiOr.make [], SimplificationProof)
  | otherwise = return $ makeEvaluateNonBoolIn first second

makeEvaluateNonBoolIn
    ::  ( SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => Pattern Object variable
    -> Pattern Object variable
    -> (Or.Pattern Object variable, SimplificationProof Object)
makeEvaluateNonBoolIn patt1 patt2 =
    ( MultiOr.make
        [ Conditional
            { term = mkTop_
            , predicate =
                makeInPredicate
                    -- TODO: Wrap in 'contained' and 'container'.
                    (Pattern.toMLPattern patt1)
                    (Pattern.toMLPattern patt2)
            , substitution = mempty
            }
        ]
    , SimplificationProof
    )
