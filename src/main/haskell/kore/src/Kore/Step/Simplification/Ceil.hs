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
    ) where

import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Map as Map

import           Kore.AST.Pure
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( makeCeilPredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..), erasePredicatedTerm,
                 predicateSubstitutionToExpandedPattern )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern, OrOfPredicateSubstitution )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make, traverseFlattenWithPairs )
import           Kore.Step.Pattern
import           Kore.Step.RecursiveAttributes
                 ( isTotalPattern )
import qualified Kore.Step.Simplification.AndPredicates as And
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Step.StepperAttributes as StepperAttributes
                 ( isTotal )
import           Kore.Unparser
import           Kore.Variables.Fresh

{-| 'simplify' simplifies a 'Ceil' of 'OrOfExpandedPattern'.

A ceil(or) is equal to or(ceil). We also take into account that
* ceil(top) = top
* ceil(bottom) = bottom
* ceil leaves predicates and substitutions unchanged
* ceil transforms terms into predicates
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
    -> PredicateSubstitutionSimplifier level Simplifier
    -> Ceil level (OrOfExpandedPattern level variable)
    -> Simplifier
        ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    tools
    substitutionSimplifier
    Ceil { ceilChild = child }
  =
    simplifyEvaluated tools substitutionSimplifier child

{-| 'simplifyEvaluated' evaluates a ceil given its child, see 'simplify'
for details.
-}
{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Ceil level) (Valid level) (OrOfExpandedPattern level variable)

instead of an 'OrOfExpandedPattern' argument. The type of 'makeEvaluate' may
be changed analogously. The 'Valid' annotation will eventually cache information
besides the pattern sort, which will make it even more useful to carry around.

-}
simplifyEvaluated
    ::  ( MetaOrObject level
        , FreshVariable variable
        , Monad m
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> OrOfExpandedPattern level variable
    -> m
        (OrOfExpandedPattern level variable, SimplificationProof level)
simplifyEvaluated tools substitutionSimplifier child = do
    (evaluated, _proofs) <-
        OrOfExpandedPattern.traverseFlattenWithPairs
            (makeEvaluate tools substitutionSimplifier)
            child
    return ( evaluated, SimplificationProof )

{-| Evaluates a ceil given its child as an ExpandedPattern, see 'simplify'
for details.
-}
makeEvaluate
    ::  ( MetaOrObject level
        , FreshVariable variable
        , Monad m
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> ExpandedPattern level variable
    -> m
        (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluate tools substitutionSimplifier child
  | ExpandedPattern.isTop child =
    return (OrOfExpandedPattern.make [ExpandedPattern.top], SimplificationProof)
  | ExpandedPattern.isBottom child =
    return (OrOfExpandedPattern.make [], SimplificationProof)
  | otherwise = makeEvaluateNonBoolCeil tools substitutionSimplifier child

makeEvaluateNonBoolCeil
    ::  ( MetaOrObject level
        , FreshVariable variable
        , Monad m
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> ExpandedPattern level variable
    -> m
        (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateNonBoolCeil
    tools
    substitutionSimplifier
    patt@Predicated {term}
  | (Recursive.project -> _ :< TopPattern _) <- term =
    return
        ( OrOfExpandedPattern.make [patt]
        , SimplificationProof
        )
  | otherwise = do
    (termCeil, _proof1) <- makeEvaluateTerm tools substitutionSimplifier term
    (result, proof) <- And.simplifyEvaluatedMultiPredicateSubstitution
        tools
        substitutionSimplifier
        [ OrOfExpandedPattern.make [erasePredicatedTerm patt]
        , termCeil
        ]
    return (fmap predicateSubstitutionToExpandedPattern result, proof)

-- TODO: Ceil(function) should be an and of all the function's conditions, both
-- implicit and explicit.
{-| Evaluates the ceil of a StepPattern, see 'simplify' for details.
-}
makeEvaluateTerm
    ::  ( MetaOrObject level
        , FreshVariable variable
        , Monad m
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> StepPattern level variable
    -> m
        (OrOfPredicateSubstitution level variable, SimplificationProof level)
makeEvaluateTerm
    tools
    substitutionSimplifier
    term@(Recursive.project -> _ :< projected)
  | TopPattern _ <- projected =
    return
        ( OrOfExpandedPattern.make [ExpandedPattern.topPredicate]
        , SimplificationProof
        )
  | BottomPattern _ <- projected =
    return
        ( OrOfExpandedPattern.make []
        , SimplificationProof
        )
  | isTotalPattern tools term =
    return
        ( OrOfExpandedPattern.make [ExpandedPattern.topPredicate]
        , SimplificationProof
        )
  | otherwise =
    case projected of
        ApplicationPattern app
          | StepperAttributes.isTotal headAttributes -> do
            simplifiedChildren <- mapM
                (makeEvaluateTerm tools substitutionSimplifier)
                children
            let
                (ceils, _proofs) = unzip simplifiedChildren
            And.simplifyEvaluatedMultiPredicateSubstitution
                tools substitutionSimplifier ceils
           where
            Application { applicationSymbolOrAlias = patternHead } = app
            Application { applicationChildren = children } = app
            headAttributes = MetadataTools.symAttributes tools patternHead
        DomainValuePattern DomainValue { domainValueChild = child } ->
            makeEvaluateBuiltin tools substitutionSimplifier child
        _ -> return
            ( OrOfExpandedPattern.make
                [Predicated
                    { term = ()
                    , predicate = makeCeilPredicate term
                    , substitution = mempty
                    }
                ]
            , SimplificationProof
            )

{-| Evaluates the ceil of a domain value.
-}
makeEvaluateBuiltin
    :: forall level variable m .
        ( level ~ Object
        , FreshVariable variable
        , Monad m
        , SortedVariable variable
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> Domain.Builtin (StepPattern level variable)
    -> m
        (OrOfPredicateSubstitution level variable, SimplificationProof level)
makeEvaluateBuiltin
    _tools
    _substitutionSimplifier
    (Domain.BuiltinExternal Domain.External { domainValueChild = p })
  =
    case Recursive.project p of
        _ :< StringLiteralPattern _ ->
            -- This should be the only kind of Domain.BuiltinExternal, and it
            -- should be valid and functional if this has passed verification.
            return
                ( OrOfExpandedPattern.make [ExpandedPattern.topPredicate]
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
    (Domain.BuiltinMap Domain.InternalMap { builtinMapChild = m })
  = do
    children <- mapM
        (makeEvaluateTerm tools substitutionSimplifier)
        values
    let
        ceils :: [OrOfPredicateSubstitution level variable]
        (ceils, _proofs) = unzip children
    And.simplifyEvaluatedMultiPredicateSubstitution
        tools substitutionSimplifier ceils
  where
    values :: [StepPattern level variable]
    -- Maps assume that their keys are relatively functional.
    values = Map.elems m
makeEvaluateBuiltin
    tools
    substitutionSimplifier
    (Domain.BuiltinList l)
  = do
    children <- mapM
        (makeEvaluateTerm tools substitutionSimplifier)
        (Foldable.toList l)
    let
        ceils :: [OrOfPredicateSubstitution level variable]
        (ceils, _proofs) = unzip children
    And.simplifyEvaluatedMultiPredicateSubstitution
        tools substitutionSimplifier ceils
makeEvaluateBuiltin _tools _substitutionSimplifier (Domain.BuiltinSet _) =
    -- Sets assume that their elements are relatively functional.
    return topPredicateWithProof
makeEvaluateBuiltin _tools _substitutionSimplifier (Domain.BuiltinBool _) =
    return topPredicateWithProof
makeEvaluateBuiltin _tools _substitutionSimplifier (Domain.BuiltinInt _) =
    return topPredicateWithProof

topPredicateWithProof
    ::  ( MetaOrObject level
        , Ord (variable level)
        )
    => (OrOfPredicateSubstitution level variable, SimplificationProof level)
topPredicateWithProof =
    ( OrOfExpandedPattern.make [ExpandedPattern.topPredicate]
    , SimplificationProof
    )
