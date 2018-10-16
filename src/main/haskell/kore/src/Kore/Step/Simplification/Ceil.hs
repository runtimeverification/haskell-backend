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

import Data.Reflection
       ( give )

import           Kore.AST.Common
                 ( Ceil (..), PureMLPattern, SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkTop )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern App_, pattern Bottom_, pattern Top_ )
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
import           Kore.Step.RecursiveAttributes
                 ( isTotalPattern )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Step.StepperAttributes as StepperAttributes
                 ( isTotal )

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
        , Show (variable level)
        , Ord (variable level)
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
simplifyEvaluated
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
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
        , Show (variable level)
        , Ord (variable level)
        )
    => MetadataTools level StepperAttributes
    -> ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluate tools child
  | ExpandedPattern.isTop child =
    (OrOfExpandedPattern.make [ExpandedPattern.top], SimplificationProof)
  | ExpandedPattern.isBottom child =
    (OrOfExpandedPattern.make [ExpandedPattern.bottom], SimplificationProof)
  | otherwise =
    makeEvaluateNonBoolCeil tools child

makeEvaluateNonBoolCeil
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        )
    => MetadataTools level StepperAttributes
    -> ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateNonBoolCeil
    _
    patt@Predicated { term = Top_ _ }
  =
    ( OrOfExpandedPattern.make [patt]
    , SimplificationProof
    )
makeEvaluateNonBoolCeil
    tools
    Predicated {term, predicate, substitution}
  =
    let
        (termCeil, _proof1) = makeEvaluateTerm tools term
        (ceilPredicate, _proof2) =
            give symbolOrAliasSorts $ makeAndPredicate predicate termCeil
    in
        ( OrOfExpandedPattern.make
            [ Predicated
                { term = mkTop
                , predicate = ceilPredicate
                , substitution = substitution
                }
            ]
        , SimplificationProof
        )
  where
    symbolOrAliasSorts = MetadataTools.symbolOrAliasSorts tools

-- TODO: Ceil(function) should be an and of all the function's conditions, both
-- implicit and explicit.
{-| Evaluates the ceil of a PureMLPattern, see 'simplify' for details.
-}
makeEvaluateTerm
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Eq (variable level)
        , Show (variable level)
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> (Predicate level variable, SimplificationProof level)
makeEvaluateTerm
    _
    (Top_ _)
  =
    (makeTruePredicate, SimplificationProof)
makeEvaluateTerm
    _
    (Bottom_ _)
  =
    (makeFalsePredicate, SimplificationProof)
makeEvaluateTerm
    tools
    term
  | isTotalPattern tools term
  =
    (makeTruePredicate, SimplificationProof)
makeEvaluateTerm
    tools
    (App_ patternHead children)
  | StepperAttributes.isTotal headAttributes
  =
    let
        (ceils, _proofs) = unzip (map (makeEvaluateTerm tools) children)
        (result, _proof) = give (MetadataTools.symbolOrAliasSorts tools )
            $ makeMultipleAndPredicate ceils
    in
        (result, SimplificationProof)
  where
    headAttributes = MetadataTools.symAttributes tools patternHead
makeEvaluateTerm
    tools term
  =
    ( give (MetadataTools.symbolOrAliasSorts tools ) $ makeCeilPredicate term
    , SimplificationProof
    )

