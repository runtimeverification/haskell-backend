module Kore.Exec
    ( exec
    , search
    ) where

import qualified Control.Arrow as Arrow
import qualified Data.Map.Merge.Strict as Map
import qualified Data.Map.Strict as Map
import           Data.Reflection
                 ( give )
import           Data.These
                 ( These (..) )

import           Data.Limit
                 ( Limit (..) )
import qualified Data.Limit as Limit
import           Kore.AST.Common
import           Kore.AST.MetaOrObject
                 ( Meta, Object (..), asUnified )
import qualified Kore.Builtin as Builtin
import           Kore.IndexedModule.IndexedModule
                 ( KoreIndexedModule )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), extractMetadataTools )

import           Kore.Predicate.Predicate
                 ( pattern PredicateTrue, makeMultipleOrPredicate,
                 makeTruePredicate, unwrapPredicate )
import           Kore.Step.AxiomPatterns
                 ( AxiomPattern (..), extractRewriteAxioms )
import           Kore.Step.BaseStep
                 ( StepProof )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.ExpandedPattern as Predicated
import           Kore.Step.Function.Registry
                 ( axiomPatternsToEvaluators, extractFunctionAxioms )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
import           Kore.Step.Search
                 ( searchTree )
import qualified Kore.Step.Search as Search
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier (..),
                 PureMLPatternSimplifier, SimplificationProof (..),
                 Simplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.Simplification.PredicateSubstitution as PredicateSubstitution
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Step.Step
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )
import           Kore.Step.Strategy
                 ( Tree )
import           Kore.Substitution.Class
                 ( Hashable, substitute )
import qualified Kore.Substitution.List as ListSubstitution
import           Kore.Variables.Fresh
                 ( FreshVariable )

exec
    :: KoreIndexedModule StepperAttributes
    -> CommonPurePattern Object
    -> Limit Natural
    -> ([AxiomPattern Object] -> Strategy (Prim (AxiomPattern Object)))
    -> Simplifier (CommonPurePattern Object)
exec indexedModule purePattern stepLimit strategy =
    helper indexedModule purePattern stepLimit strategy execute
  where
    execute
        :: MetadataTools Object StepperAttributes
        -> PureMLPatternSimplifier Object Variable
        -> PredicateSubstitutionSimplifier Object Simplifier
        -> Tree (CommonExpandedPattern Object, StepProof Object Variable)
        -> Simplifier (CommonPurePattern Object)
    execute metadataTools _ _ executionTree =
        give (symbolOrAliasSorts metadataTools) $ do
            let (finalConfig, _) = pickLongest executionTree
            return (ExpandedPattern.toMLPattern finalConfig)

search
    :: KoreIndexedModule StepperAttributes
    -> CommonPurePattern Object
    -> Limit Natural
    -> ([AxiomPattern Object] -> Strategy (Prim (AxiomPattern Object)))
    -> CommonExpandedPattern Object
    -> Search.Config
    -> Simplifier (CommonPurePattern Object)
search
    indexedModule
    purePattern
    stepLimit
    strategy
    searchPattern
    searchConfig
  =
    helper indexedModule purePattern stepLimit strategy execute
  where
    execute metadataTools simplifier substitutionSimplifier executionTree = do
        let
            match target (config, _proof) =
                Search.matchWith
                    metadataTools
                    substitutionSimplifier
                    simplifier
                    target
                    config
        solutions <- searchTree searchConfig (match searchPattern) executionTree
        let
            orPredicate =
                give (symbolOrAliasSorts metadataTools)
                $ makeMultipleOrPredicate
                $ fmap Predicated.toPredicate solutions
        return (unwrapPredicate orPredicate)

helper
    :: KoreIndexedModule StepperAttributes
    -> CommonPurePattern Object
    -> Limit Natural
    -> ([AxiomPattern Object] -> Strategy (Prim (AxiomPattern Object)))
    -> (MetadataTools Object StepperAttributes
        -> PureMLPatternSimplifier Object Variable
        -> PredicateSubstitutionSimplifier Object Simplifier
        -> Tree (CommonExpandedPattern Object, StepProof Object Variable)
        -> Simplifier a)
    -> Simplifier a
helper indexedModule purePattern stepLimit strategy execute = do
    let
        metadataTools = extractMetadataTools indexedModule
    axiomsAndSimplifiers <-
        makeAxiomsAndSimplifiers indexedModule metadataTools
    let
        (rewriteAxioms, simplifier, substitutionSimplifier) =
            axiomsAndSimplifiers
        runStrategy' pat =
            runStrategy
                (transitionRule metadataTools substitutionSimplifier simplifier)
                (Limit.replicate stepLimit (strategy rewriteAxioms))
                (pat, mempty)
        expandedPattern = makeExpandedPattern purePattern
    simplifiedPatterns <-
        ExpandedPattern.simplify
            metadataTools substitutionSimplifier simplifier expandedPattern
    let
        initialPattern =
            case OrOfExpandedPattern.extractPatterns (fst simplifiedPatterns) of
                [] -> ExpandedPattern.bottom
                (config : _) -> config
    executionTree <- runStrategy' initialPattern
    execute metadataTools simplifier substitutionSimplifier executionTree

makeExpandedPattern
    :: CommonPurePattern Object
    -> CommonExpandedPattern Object
makeExpandedPattern pat =
    Predicated
    { term = pat
    , predicate = makeTruePredicate
    , substitution = []
    }

preSimplify
    ::  (  CommonPurePattern Object
        -> Simplifier
            (OrOfExpandedPattern Object Variable, SimplificationProof Object)
        )
    -> AxiomPattern Object
    -> Simplifier (AxiomPattern Object)
preSimplify simplifier
    AxiomPattern
    { axiomPatternLeft = lhs
    , axiomPatternRight = rhs
    , axiomPatternRequires = requires
    , axiomPatternAttributes = atts
    }
  = do
    (simplifiedOrLhs, _proof) <- simplifier lhs
    let
        [Predicated {term, predicate = PredicateTrue, substitution}] =
            OrOfExpandedPattern.extractPatterns simplifiedOrLhs
        listSubst =
            ListSubstitution.fromList
                (map (Arrow.first asUnified) substitution)
    newLhs <- substitute term listSubst
    newRhs <- substitute rhs listSubst
    newRequires <- traverse (`substitute` listSubst) requires
    return AxiomPattern
        { axiomPatternLeft = newLhs
        , axiomPatternRight = newRhs
        , axiomPatternRequires = newRequires
        , axiomPatternAttributes = atts
        }

makeAxiomsAndSimplifiers
    :: KoreIndexedModule StepperAttributes
    -> MetadataTools Object StepperAttributes
    -> Simplifier
        ( [AxiomPattern Object]
        , PureMLPatternSimplifier Object Variable
        , PredicateSubstitutionSimplifier Object Simplifier
        )
makeAxiomsAndSimplifiers indexedModule tools =
    do
        functionAxioms <-
            simplifyFunctionAxioms
                (extractFunctionAxioms Object indexedModule)
        rewriteAxioms <-
            simplifyRewriteAxioms
                (extractRewriteAxioms Object indexedModule)
        let
            functionEvaluators =
                axiomPatternsToEvaluators functionAxioms
            functionRegistry =
                Map.merge
                    (Map.mapMissing (const This))
                    (Map.mapMissing (const That))
                    (Map.zipWithMatched (const These))
                    -- builtin functions
                    (Builtin.koreEvaluators indexedModule)
                    -- user-defined functions
                    functionEvaluators
            simplifier
                ::  ( SortedVariable variable
                    , Ord (variable Meta)
                    , Ord (variable Object)
                    , Show (variable Meta)
                    , Show (variable Object)
                    , FreshVariable variable
                    , Hashable variable
                    )
                => PureMLPatternSimplifier Object variable
            simplifier = Simplifier.create tools functionRegistry
            substitutionSimplifier
                :: PredicateSubstitutionSimplifier Object Simplifier
            substitutionSimplifier =
                PredicateSubstitution.create tools simplifier
        return (rewriteAxioms, simplifier, substitutionSimplifier)
  where
    simplifyFunctionAxioms = mapM (mapM (preSimplify emptyPatternSimplifier))
    simplifyRewriteAxioms = mapM (preSimplify emptyPatternSimplifier)
    emptySimplifier
        ::  ( SortedVariable variable
            , Ord (variable Meta)
            , Ord (variable Object)
            , Show (variable Meta)
            , Show (variable Object)
            , FreshVariable variable
            , Hashable variable
            )
        => PureMLPatternSimplifier Object variable
    emptySimplifier = Simplifier.create tools Map.empty
    emptySubstitutionSimplifier =
        PredicateSubstitution.create tools emptySimplifier
    emptyPatternSimplifier =
        ExpandedPattern.simplify
            tools
            emptySubstitutionSimplifier
            emptySimplifier
        . makeExpandedPattern
