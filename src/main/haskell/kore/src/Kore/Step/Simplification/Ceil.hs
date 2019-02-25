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
import           Kore.AST.Valid
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( Predicate, makeAndPredicate, makeCeilPredicate,
                 makeFalsePredicate, makeMultipleAndPredicate,
                 makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( fmapFlattenWithPairs, make )
import           Kore.Step.Pattern
import           Kore.Step.RecursiveAttributes
                 ( isTotalPattern )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Step.StepperAttributes as StepperAttributes
                 ( isTotal )
import           Kore.Unparser

{-| 'simplify' simplifies a 'Ceil' of 'OrOfExpandedPattern'.

A ceil(or) is equal to or(ceil). We also take into account that
* ceil(top) = top
* ceil(bottom) = bottom
* ceil leaves predicates and substitutions unchanged
* ceil transforms terms into predicates
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> Ceil level (OrOfExpandedPattern level variable)
    ->  ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    tools
    Ceil { ceilChild = child }
  =
    simplifyEvaluated tools child

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
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> OrOfExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
simplifyEvaluated tools child =
    ( evaluated, SimplificationProof )
  where
    (evaluated, _proofs) =
        OrOfExpandedPattern.fmapFlattenWithPairs (makeEvaluate tools) child

{-| Evaluates a ceil given its child as an ExpandedPattern, see 'simplify'
for details.
-}
makeEvaluate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluate tools child
  | ExpandedPattern.isTop child =
    (OrOfExpandedPattern.make [ExpandedPattern.top], SimplificationProof)
  | ExpandedPattern.isBottom child =
    (OrOfExpandedPattern.make [ExpandedPattern.bottom], SimplificationProof)
  | otherwise = makeEvaluateNonBoolCeil tools child

makeEvaluateNonBoolCeil
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateNonBoolCeil
    tools
    patt@Predicated {term, predicate, substitution}
  | (Recursive.project -> _ :< TopPattern _) <- term =
    ( OrOfExpandedPattern.make [patt]
    , SimplificationProof
    )
  | otherwise =
    let
        (termCeil, _proof1) = makeEvaluateTerm tools term
        ceilPredicate = makeAndPredicate predicate termCeil
    in
        ( OrOfExpandedPattern.make
            [ Predicated
                { term = mkTop_
                , predicate = ceilPredicate
                , substitution = substitution
                }
            ]
        , SimplificationProof
        )

-- TODO: Ceil(function) should be an and of all the function's conditions, both
-- implicit and explicit.
{-| Evaluates the ceil of a StepPattern, see 'simplify' for details.
-}
makeEvaluateTerm
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> StepPattern level variable
    -> (Predicate level variable, SimplificationProof level)
makeEvaluateTerm
    tools
    term@(Recursive.project -> _ :< projected)
  | TopPattern _ <- projected =
    (makeTruePredicate, SimplificationProof)
  | BottomPattern _ <- projected =
    (makeFalsePredicate, SimplificationProof)
  | isTotalPattern tools term = -- trace ("###Simp.Ceil.isTotalPattern" ++ show term)
    (makeTruePredicate, SimplificationProof)
  | otherwise =
    case projected of
        ApplicationPattern app
          | StepperAttributes.isTotal headAttributes ->
            let
                (ceils, _proofs) = unzip (map (makeEvaluateTerm tools) children)
                result = makeMultipleAndPredicate ceils
            in
                (result, SimplificationProof)
          where
            Application { applicationSymbolOrAlias = patternHead } = app
            Application { applicationChildren = children } = app
            headAttributes = MetadataTools.symAttributes tools patternHead
        DomainValuePattern DomainValue { domainValueChild = child } ->
            makeEvaluateBuiltin tools child
        _ ->
            (makeCeilPredicate term, SimplificationProof)

{-| Evaluates the ceil of a domain value.
-}
makeEvaluateBuiltin
    :: forall level variable .
        ( level ~ Object
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> Domain.Builtin (StepPattern level variable)
    -> (Predicate level variable, SimplificationProof level)
makeEvaluateBuiltin
    _tools
    (Domain.BuiltinPattern p)
  =
    case Recursive.project p of
        _ :< StringLiteralPattern _ ->
            -- This should be the only kind of Domain.BuiltinPattern, and it
            -- should be valid and functional if this has passed verification.
            (makeTruePredicate, SimplificationProof)
        _ ->
            error
                ( "Ceil not implemented: non-string pattern."
                ++ show p
                )
makeEvaluateBuiltin
    tools
    (Domain.BuiltinMap m)
  =
    (makeMultipleAndPredicate ceils, SimplificationProof)
  where
    values :: [StepPattern level variable]
    -- Maps assume that their keys are relatively functional.
    values = Map.elems m
    ceils :: [Predicate level variable]
    (ceils, _proofs) = unzip (map (makeEvaluateTerm tools) values)
makeEvaluateBuiltin
    tools
    (Domain.BuiltinList l)
  =
    (makeMultipleAndPredicate ceils, SimplificationProof)
  where
    ceils :: [Predicate level variable]
    (ceils, _proofs) = unzip (map (makeEvaluateTerm tools) (Foldable.toList l))
makeEvaluateBuiltin
    _
    (Domain.BuiltinSet _)
  =
    -- Sets assume that their elements are relatively functional.
    (makeTruePredicate, SimplificationProof)
makeEvaluateBuiltin _tools _ = (makeTruePredicate, SimplificationProof)
