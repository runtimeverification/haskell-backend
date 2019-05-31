{-|
Module      : Kore.Step.Simplification.Ceil
Description : Tools for Ceil pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Ceil
    ( simplify
    , makeEvaluate
    , makeEvaluateTerm
    , simplifyEvaluated
    , Ceil (..)
    ) where

import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Map as Map

import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import qualified Kore.Attribute.Symbol as StepperAttributes
                 ( isTotal )
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Internal.Conditional
                 ( Conditional (..) )
import qualified Kore.Internal.MultiAnd as MultiAnd
                 ( make )
import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.OrPredicate
                 ( OrPredicate )
import qualified Kore.Internal.OrPredicate as OrPredicate
import           Kore.Internal.Pattern
                 ( Pattern )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( makeCeilPredicate, makeTruePredicate )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Function.Evaluator as Axiom
                 ( evaluatePattern )
import           Kore.Step.RecursiveAttributes
                 ( isTotalPattern )
import qualified Kore.Step.Simplification.AndPredicates as And
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, Simplifier, TermLikeSimplifier )
import qualified Kore.Step.Simplification.Data as Simplifier
import           Kore.TopBottom
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

{-| Simplify a 'Ceil' of 'OrPattern'.

A ceil(or) is equal to or(ceil). We also take into account that
* ceil(top) = top
* ceil(bottom) = bottom
* ceil leaves predicates and substitutions unchanged
* ceil transforms terms into predicates
-}
simplify
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        )
    => PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> Ceil Sort (OrPattern variable)
    -> Simplifier (OrPattern variable)
simplify
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    Ceil { ceilChild = child }
  =
    simplifyEvaluated substitutionSimplifier simplifier axiomIdToEvaluator child

{-| 'simplifyEvaluated' evaluates a ceil given its child, see 'simplify'
for details.
-}
{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Ceil Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of an 'OrPattern' argument. The type of 'makeEvaluate' may
be changed analogously. The 'Attribute.Pattern' annotation will eventually cache
information besides the pattern sort, which will make it even more useful to
carry around.

-}
simplifyEvaluated
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        )
    => PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> OrPattern variable
    -> Simplifier (OrPattern variable)
simplifyEvaluated
    substitutionSimplifier simplifier axiomIdToEvaluator child
  = do
    evaluated <-
        traverse
            (makeEvaluate
                substitutionSimplifier
                simplifier
                axiomIdToEvaluator
            )
            child
    return (MultiOr.flatten evaluated)

{-| Evaluates a ceil given its child as an Pattern, see 'simplify'
for details.
-}
makeEvaluate
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        )
    => PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> Pattern variable
    -> Simplifier (OrPattern variable)
makeEvaluate substitutionSimplifier simplifier axiomIdToEvaluator child
  | Pattern.isTop    child = return (OrPattern.top)
  | Pattern.isBottom child = return (OrPattern.bottom)
  | otherwise =
    makeEvaluateNonBoolCeil
        substitutionSimplifier
        simplifier
        axiomIdToEvaluator
        child

makeEvaluateNonBoolCeil
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        )
    => PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> Pattern variable
    -> Simplifier (OrPattern variable)
makeEvaluateNonBoolCeil
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    patt@Conditional {term}
  | isTop term = return $ OrPattern.fromPattern patt
  | otherwise = do
    tools <- Simplifier.askMetadataTools
    termCeil <-
        makeEvaluateTerm
            tools
            substitutionSimplifier
            simplifier
            axiomIdToEvaluator
            term
    result <-
        And.simplifyEvaluatedMultiPredicate
            tools
            substitutionSimplifier
            simplifier
            axiomIdToEvaluator
            (MultiAnd.make
                [ MultiOr.make [Predicate.eraseConditionalTerm patt]
                , termCeil
                ]
            )
    return (fmap Pattern.fromPredicate result)

-- TODO: Ceil(function) should be an and of all the function's conditions, both
-- implicit and explicit.
{-| Evaluates the ceil of a TermLike, see 'simplify' for details.
-}
-- NOTE (hs-boot): Please update Ceil.hs-boot file when changing the
-- signature.
makeEvaluateTerm
    ::  forall variable .
        ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> TermLike variable
    -> Simplifier (OrPredicate variable)
makeEvaluateTerm
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    term@(Recursive.project -> _ :< projected)
  | isTop term                = return OrPredicate.top
  | isBottom term             = return OrPredicate.bottom
  | isTotalPattern tools term = return OrPredicate.top
  | otherwise =
    case projected of
        ApplicationF app
          | StepperAttributes.isTotal headAttributes -> do
            simplifiedChildren <- mapM
                (makeEvaluateTerm
                    tools substitutionSimplifier simplifier axiomIdToEvaluator
                )
                children
            let ceils = simplifiedChildren
            And.simplifyEvaluatedMultiPredicate
                tools
                substitutionSimplifier
                simplifier
                axiomIdToEvaluator
                (MultiAnd.make ceils)
          where
            Application { applicationSymbolOrAlias = patternHead } = app
            Application { applicationChildren = children } = app
            headAttributes = MetadataTools.symAttributes tools patternHead
        BuiltinF child ->
            makeEvaluateBuiltin
                tools
                substitutionSimplifier
                simplifier
                axiomIdToEvaluator
                child
        _ -> do
            evaluation <- Axiom.evaluatePattern
                substitutionSimplifier
                simplifier
                axiomIdToEvaluator
                Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                (mkCeil_ term)
                (OrPattern.fromPattern Conditional
                    { term = mkTop_
                    , predicate = makeCeilPredicate term
                    , substitution = mempty
                    }
                )
            return (fmap toPredicate evaluation)
  where
    toPredicate Conditional {term = Top_ _, predicate, substitution} =
        Conditional {term = (), predicate, substitution}
    toPredicate patt =
        error
            (  "Ceil simplification is expected to result ai a predicate, but"
            ++ " got (" ++ show patt ++ ")."
            ++ " The most likely cases are: evaluating predicate symbols, "
            ++ " and predicate symbols are currently unrecognized as such, "
            ++ "and programming errors."
            )

{-| Evaluates the ceil of a domain value.
-}
makeEvaluateBuiltin
    :: forall variable .
        ( FreshVariable variable
        , SortedVariable variable
        , Unparse variable
        , Show variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> Builtin (TermLike variable)
    -> Simplifier (OrPredicate variable)
makeEvaluateBuiltin
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    (Domain.BuiltinMap Domain.InternalMap { builtinMapChild = m })
  = do
    children <- mapM
        (makeEvaluateTerm
            tools substitutionSimplifier simplifier axiomIdToEvaluator
        )
        values
    let
        ceils :: [OrPredicate variable]
        ceils = children
    And.simplifyEvaluatedMultiPredicate
        tools
        substitutionSimplifier
        simplifier
        axiomIdToEvaluator
        (MultiAnd.make ceils)
  where
    values :: [TermLike variable]
    -- Maps assume that their keys are relatively functional.
    values = Map.elems m
makeEvaluateBuiltin
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    (Domain.BuiltinList l)
  = do
    children <- mapM
        (makeEvaluateTerm
            tools substitutionSimplifier simplifier axiomIdToEvaluator
        )
        (Foldable.toList l)
    let
        ceils :: [OrPredicate variable]
        ceils = children
    And.simplifyEvaluatedMultiPredicate
        tools
        substitutionSimplifier
        simplifier
        axiomIdToEvaluator
        (MultiAnd.make ceils)
makeEvaluateBuiltin
    _tools
    _substitutionSimplifier
    _simplifier
    _axiomIdToSimplifier
    (Domain.BuiltinSet _)
  =
    -- Sets assume that their elements are relatively functional.
    return OrPredicate.top
makeEvaluateBuiltin
    _tools
    _substitutionSimplifier
    _simplifier
    _axiomIdToSimplifier
    (Domain.BuiltinBool _)
  =
    return OrPredicate.top
makeEvaluateBuiltin
    _tools
    _substitutionSimplifier
    _simplifier
    _axiomIdToSimplifier
    (Domain.BuiltinInt _)
  =
    return OrPredicate.top
makeEvaluateBuiltin
    _tools
    _substitutionSimplifier
    _simplifier
    _axiomIdToSimplifier
    (Domain.BuiltinString _)
  =
    return OrPredicate.top
