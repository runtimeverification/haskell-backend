{-|
Module      : Kore.Step.Simplification.Exists
Description : Tools for Exists pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Exists
    ( simplify
    , makeEvaluate
    ) where

import qualified Control.Arrow as Arrow
import           Data.Reflection
                 ( Given )
import qualified Data.Set as Set

import           Kore.AST.Common
                 ( Exists (..), SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkExists )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools, SymbolOrAliasSorts )
import           Kore.Predicate.Predicate
                 ( Predicate, makeExistsPredicate, makeTruePredicate,
                 unwrapPredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( toMLPattern )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( isFalse, isTrue, make, traverseFlattenWithPairs )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier (..) )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
                 ( simplify )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Substitution.Class
                 ( Hashable (..), substitute )
import qualified Kore.Substitution.List as ListSubstitution
import           Kore.Unification.Unifier
                 ( UnificationSubstitution )
import           Kore.Variables.Free
                 ( freePureVariables )
import           Kore.Variables.Fresh

-- TODO: Move Exists up in the other simplifiers or something similar. Note
-- that it messes up top/bottom testing so moving it up must be done
-- immediately after evaluating the children.
{-|'simplify' simplifies an 'Exists' pattern with an 'OrOfExpandedPattern'
child.

The simplification of exists x . (pat and pred and subst) is equivalent to:

* If the subst contains an assignment for x, then substitute that in pat and
  pred, reevaluate them and return
  (reevaluated-pat and reevaluated-pred and subst-without-x).
* Otherwise, if x does not occur free in pat and pred, return
  (pat and pred and subst)
* Otherwise, if x does not occur free in pat, return
  (pat and (exists x . pred) and subst)
* Otherwise, if x does not occur free in pred, return
  ((exists x . pat) and pred and subst)
* Otherwise return
  ((exists x . pat and pred) and subst)
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SymbolOrAliasSorts level)
        , Show (variable level)
        , Ord (variable level)
        , Show (variable Meta)
        , Show (variable Object)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Hashable variable
        , FreshVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -- ^ Simplifies patterns.
    -> Exists level variable (OrOfExpandedPattern level variable)
    -> Simplifier
        ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    tools
    substitutionSimplifier
    simplifier
    Exists { existsVariable = variable, existsChild = child }
  =
    simplifyEvaluated tools substitutionSimplifier simplifier variable child

simplifyEvaluated
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SymbolOrAliasSorts level)
        , Show (variable level)
        , Ord (variable level)
        , Show (variable Meta)
        , Show (variable Object)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Hashable variable
        , FreshVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -- ^ Simplifies patterns.
    -> variable level
    -> OrOfExpandedPattern level variable
    -> Simplifier
        (OrOfExpandedPattern level variable, SimplificationProof level)
simplifyEvaluated tools substitutionSimplifier simplifier variable simplified
  | OrOfExpandedPattern.isTrue simplified =
    return (simplified, SimplificationProof)
  | OrOfExpandedPattern.isFalse simplified =
    return (simplified, SimplificationProof)
  | otherwise = do
    (evaluated, _proofs) <-
        OrOfExpandedPattern.traverseFlattenWithPairs
            (makeEvaluate tools substitutionSimplifier simplifier variable)
            simplified
    return ( evaluated, SimplificationProof )

{-| evaluates an 'Exists' given its two 'ExpandedPattern' children.

See 'simplify' for detailed documentation.
-}
makeEvaluate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SymbolOrAliasSorts level)
        , Show (variable level)
        , Ord (variable level)
        , Show (variable Meta)
        , Show (variable Object)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Hashable variable
        , FreshVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -- ^ Simplifies patterns.
    -> variable level
    -> ExpandedPattern level variable
    -> Simplifier
        (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluate
    tools
    substitutionSimplifier
    simplifier
    variable
    patt@Predicated { term, predicate, substitution }
  =
    case localSubstitution of
        [] ->
            return (makeEvaluateNoFreeVarInSubstitution variable patt)
        _ -> do
            (substitutedPat, _proof) <-
                substituteTermPredicate
                    term
                    predicate
                    localSubstitutionList
                    globalSubstitution
            (result, _proof) <-
                ExpandedPattern.simplify
                    tools substitutionSimplifier simplifier substitutedPat
            return (result , SimplificationProof)
  where
    (Local localSubstitution, Global globalSubstitution) =
        splitSubstitutionByVariable variable substitution
    localSubstitutionList =
        ListSubstitution.fromList
            (map (Arrow.first asUnified) localSubstitution)

makeEvaluateNoFreeVarInSubstitution
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SymbolOrAliasSorts level)
        , Show (variable level)
        , Ord (variable level)
        , Show (variable Meta)
        , Show (variable Object)
        , Ord (variable Meta)
        , Ord (variable Object)
        )
    => variable level
    -> ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateNoFreeVarInSubstitution
    variable
    patt@Predicated { term, predicate, substitution }
  =
    (OrOfExpandedPattern.make [simplifiedPattern], SimplificationProof)
  where
    termHasVariable =
        Set.member variable (freePureVariables term)
    predicateHasVariable =
        Set.member variable (freePureVariables $ unwrapPredicate predicate)
    simplifiedPattern = case (termHasVariable, predicateHasVariable) of
        (False, False) -> patt
        (False, True) ->
            let
                predicate' = makeExistsPredicate variable predicate
            in
                Predicated
                    { term = term
                    , predicate = predicate'
                    , substitution = substitution
                    }
        (True, False) ->
            Predicated
                { term = mkExists variable term
                , predicate = predicate
                , substitution = substitution
                }
        (True, True) ->
            Predicated
                { term =
                    mkExists variable
                        (ExpandedPattern.toMLPattern
                            Predicated
                                { term = term
                                , predicate = predicate
                                , substitution = []
                                }
                        )
                , predicate = makeTruePredicate
                , substitution = substitution
                }

substituteTermPredicate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SymbolOrAliasSorts level)
        , Show (variable level)
        , Ord (variable level)
        , Show (variable Meta)
        , Show (variable Object)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Hashable variable
        , FreshVariable variable
        )
    => StepPattern level variable
    -> Predicate level variable
    -> ListSubstitution.Substitution (Unified variable) (StepPattern level variable)
    -> UnificationSubstitution level variable
    -> Simplifier
        (ExpandedPattern level variable, SimplificationProof level)
substituteTermPredicate term predicate substitution globalSubstitution = do
    substitutedTerm <- substitute term substitution
    substitutedPredicate <-
        traverse (`substitute` substitution) predicate
    return
        ( Predicated
            { term = substitutedTerm
            , predicate = substitutedPredicate
            , substitution = globalSubstitution
            }
        , SimplificationProof
        )

newtype Local a = Local a
newtype Global a = Global a

splitSubstitutionByVariable
    :: Eq (variable level)
    => variable level
    -> UnificationSubstitution level variable
    ->  ( Local (UnificationSubstitution level variable)
        , Global (UnificationSubstitution level variable)
        )
splitSubstitutionByVariable _ [] =
    (Local [], Global [])
splitSubstitutionByVariable variable ((var, term) : substs)
  | var == variable =
    (Local [(var, term)], Global substs)
  | otherwise =
    (local, Global ((var, term) : global))
  where
    (local, Global global) = splitSubstitutionByVariable variable substs
