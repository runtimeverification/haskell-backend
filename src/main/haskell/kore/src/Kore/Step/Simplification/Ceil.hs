{-|
Module      : Kore.Simplification.Ceil
Description : Tools for Ceil pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Ceil
    ( simplify
    , makeEvaluate
    , simplifyEvaluated
    ) where

import Data.Either
       ( isRight )
import Data.Reflection
       ( give )

import           Kore.AST.Common
                 ( Ceil (..), SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( PureMLPattern )
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
                 ( ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), bottom, isBottom, isTop, top )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( fmapFlattenWithPairs, make )
import           Kore.Step.PatternAttributes
                 ( isFunctionalPattern )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Step.StepperAttributes as StepperAttributes
                 ( StepperAttributes (..) )

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
    -> Ceil level (OrOfExpandedPattern level domain variable)
    ->  ( OrOfExpandedPattern level domain variable
        , ()
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
    -> OrOfExpandedPattern level domain variable
    -> (OrOfExpandedPattern level domain variable, ())
simplifyEvaluated tools child =
    ( evaluated, () )
  where
    (evaluated, _) =
        OrOfExpandedPattern.fmapFlattenWithPairs (makeEvaluate tools) child

{-| 'simplifyEvaluated' evaluates a ceil given its child as
an ExpandedPattern, see 'simplify' for details.
-}
makeEvaluate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        )
    => MetadataTools level StepperAttributes
    -> ExpandedPattern level domain variable
    -> (OrOfExpandedPattern level domain variable, ())
makeEvaluate tools child
  | ExpandedPattern.isTop child =
    (OrOfExpandedPattern.make [ExpandedPattern.top], ())
  | ExpandedPattern.isBottom child =
    (OrOfExpandedPattern.make [ExpandedPattern.bottom], ())
  | otherwise =
    makeEvaluateNonBoolCeil tools child

makeEvaluateNonBoolCeil
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        )
    => MetadataTools level StepperAttributes
    -> ExpandedPattern level domain variable
    -> (OrOfExpandedPattern level domain variable, ())
makeEvaluateNonBoolCeil
    _
    patt@ExpandedPattern { term = Top_ _ }
  =
    ( OrOfExpandedPattern.make [patt]
    , ()
    )
makeEvaluateNonBoolCeil
    tools
    ExpandedPattern {term, predicate, substitution}
  =
    let
        (termCeil, _) = makeTermCeil tools term
        (ceilPredicate, _) =
            give sortTools $ makeAndPredicate predicate termCeil
    in
        ( OrOfExpandedPattern.make
            [ ExpandedPattern
                { term = mkTop
                , predicate = ceilPredicate
                , substitution = substitution
                }
            ]
        , ()
        )
  where
    sortTools = MetadataTools.sortTools tools

-- TODO: Ceil(function) should be an and of all the function's conditions, both
-- implicit and explicit.
makeTermCeil
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level domain variable
    -> (Predicate level domain variable, ())
makeTermCeil
    _
    (Top_ _)
  =
    (makeTruePredicate, ())
makeTermCeil
    _
    (Bottom_ _)
  =
    (makeFalsePredicate, ())
makeTermCeil
    tools
    term
  | isFunctional tools term
  =
    (makeTruePredicate, ())
makeTermCeil
    tools
    (App_ patternHead children)
  | StepperAttributes.isFunctional headAttributes
      || StepperAttributes.isConstructor headAttributes
  =
    let
        (ceils, _) = unzip (map (makeTermCeil tools) children)
        (result, _) = give (MetadataTools.sortTools tools )
            $ makeMultipleAndPredicate ceils
    in
        (result, ())
  where
    headAttributes = MetadataTools.attributes tools patternHead
makeTermCeil
    tools term
  =
    ( give (MetadataTools.sortTools tools ) $ makeCeilPredicate term
    , ()
    )

-- TODO: Move these somewhere reasonable and remove all of their other
-- definitions.
isFunctional
    :: MetadataTools level StepperAttributes
    -> PureMLPattern level domain variable
    -> Bool
isFunctional tools term =
    isRight (isFunctionalPattern tools term)
