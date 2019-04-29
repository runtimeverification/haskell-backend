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

import qualified Kore.AST.Common as Common
import           Kore.AST.Valid
                 ( pattern Top_, mkCeil_, mkTop_ )
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import qualified Kore.Attribute.Symbol as StepperAttributes
                 ( isTotal )
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( makeCeilPredicate, makeTruePredicate )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Conditional
                 ( Conditional (..) )
import qualified Kore.Step.Function.Evaluator as Axiom
                 ( evaluatePattern )
import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.OrPredicate
                 ( OrPredicate )
import           Kore.Step.Pattern
                 ( Pattern )
import qualified Kore.Step.Pattern as Pattern
import qualified Kore.Step.Predicate as Predicate
import           Kore.Step.RecursiveAttributes
                 ( isTotalPattern )
import qualified Kore.Step.Representation.MultiAnd as MultiAnd
                 ( make )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make, traverseFlattenWithPairs )
import qualified Kore.Step.Simplification.AndPredicates as And
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, SimplificationProof (..), Simplifier,
                 TermLikeSimplifier )
import           Kore.Step.TermLike
import           Kore.Syntax.Application
import           Kore.Syntax.Ceil
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
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier Object
    -> TermLikeSimplifier Object
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from symbol IDs to defined functions
    -> Ceil Object (OrPattern Object variable)
    -> Simplifier
        ( OrPattern Object variable
        , SimplificationProof Object
        )
simplify
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    Ceil { ceilChild = child }
  =
    simplifyEvaluated
        tools substitutionSimplifier simplifier axiomIdToEvaluator child

{-| 'simplifyEvaluated' evaluates a ceil given its child, see 'simplify'
for details.
-}
{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Ceil Object) (Valid Object) (OrPattern Object variable)

instead of an 'OrPattern' argument. The type of 'makeEvaluate' may
be changed analogously. The 'Valid' annotation will eventually cache information
besides the pattern sort, which will make it even more useful to carry around.

-}
simplifyEvaluated
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier Object
    -> TermLikeSimplifier Object
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from symbol IDs to defined functions
    -> OrPattern Object variable
    -> Simplifier
        (OrPattern Object variable, SimplificationProof Object)
simplifyEvaluated
    tools substitutionSimplifier simplifier axiomIdToEvaluator child
  = do
    (evaluated, _proofs) <-
        MultiOr.traverseFlattenWithPairs
            (makeEvaluate
                tools
                substitutionSimplifier
                simplifier
                axiomIdToEvaluator
            )
            child
    return ( evaluated, SimplificationProof )

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
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier Object
    -> TermLikeSimplifier Object
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from symbol IDs to defined functions
    -> Pattern Object variable
    -> Simplifier
        (OrPattern Object variable, SimplificationProof Object)
makeEvaluate tools substitutionSimplifier simplifier axiomIdToEvaluator child
  | Pattern.isTop    child = return (OrPattern.top, SimplificationProof)
  | Pattern.isBottom child = return (OrPattern.bottom, SimplificationProof)
  | otherwise =
        makeEvaluateNonBoolCeil
            tools
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
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier Object
    -> TermLikeSimplifier Object
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from symbol IDs to defined functions
    -> Pattern Object variable
    -> Simplifier
        (OrPattern Object variable, SimplificationProof Object)
makeEvaluateNonBoolCeil
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    patt@Conditional {term}
  | isTop term =
    return
        ( OrPattern.fromPattern patt
        , SimplificationProof
        )
  | otherwise = do
    (termCeil, _proof1) <- makeEvaluateTerm
        tools
        substitutionSimplifier
        simplifier
        axiomIdToEvaluator
        term
    (result, proof) <- And.simplifyEvaluatedMultiPredicate
        tools
        substitutionSimplifier
        simplifier
        axiomIdToEvaluator
        (MultiAnd.make
            [ MultiOr.make [Predicate.eraseConditionalTerm patt]
            , termCeil
            ]
        )
    return (fmap Pattern.fromPredicate result, proof)

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
    -> PredicateSimplifier Object
    -> TermLikeSimplifier Object
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from symbol IDs to defined functions
    -> TermLike variable
    -> Simplifier (OrPredicate Object variable, SimplificationProof Object)
makeEvaluateTerm
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    term@(Recursive.project -> _ :< projected)
  | isTop term =
    return
        ( MultiOr.make [Predicate.top]
        , SimplificationProof
        )
  | isBottom term =
    return (MultiOr.make [], SimplificationProof)
  | isTotalPattern tools term =
    return
        ( MultiOr.make [Predicate.top]
        , SimplificationProof
        )
  | otherwise =
    case projected of
        Common.ApplicationPattern app
          | StepperAttributes.isTotal headAttributes -> do
            simplifiedChildren <- mapM
                (makeEvaluateTerm
                    tools substitutionSimplifier simplifier axiomIdToEvaluator
                )
                children
            let
                (ceils, _proofs) = unzip simplifiedChildren
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
        Common.DomainValuePattern child ->
            makeEvaluateBuiltin
                tools
                substitutionSimplifier
                simplifier
                axiomIdToEvaluator
                child
        _ -> do
            (evaluation, proof) <- Axiom.evaluatePattern
                tools
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
            return (fmap toPredicate evaluation, proof)
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
        ( Object ~ Object
        , FreshVariable variable
        , SortedVariable variable
        , Unparse variable
        , Show variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier Object
    -> TermLikeSimplifier Object
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from symbol IDs to defined functions
    -> Domain.Builtin (TermLike variable)
    -> Simplifier
        (OrPredicate Object variable, SimplificationProof Object)
makeEvaluateBuiltin
    _tools
    _substitutionSimplifier
    _simplifier
    _axiomIdToSimplifier
    (Domain.BuiltinExternal Domain.External { domainValueChild = p })
  =
    case Recursive.project p of
        _ :< Common.StringLiteralPattern _ ->
            -- This should be the only kind of Domain.BuiltinExternal, and it
            -- should be valid and functional if this has passed verification.
            return
                ( MultiOr.make [Predicate.top]
                , SimplificationProof
                )
        _ ->
            error
                ( "Ceil not implemented: non-string pattern."
                ++ show p
                )
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
        ceils :: [OrPredicate Object variable]
        (ceils, _proofs) = unzip children
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
        ceils :: [OrPredicate Object variable]
        (ceils, _proofs) = unzip children
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
    return topPredicateWithProof
makeEvaluateBuiltin
    _tools
    _substitutionSimplifier
    _simplifier
    _axiomIdToSimplifier
    (Domain.BuiltinBool _)
  =
    return topPredicateWithProof
makeEvaluateBuiltin
    _tools
    _substitutionSimplifier
    _simplifier
    _axiomIdToSimplifier
    (Domain.BuiltinInt _)
  =
    return topPredicateWithProof

topPredicateWithProof
    :: Ord variable
    => (OrPredicate Object variable, SimplificationProof Object)
topPredicateWithProof =
    ( MultiOr.make [Predicate.top]
    , SimplificationProof
    )
