{-|
Module      : Kore.Exec
Description : Expose concrete execution as a library
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Stability   : experimental
Portability : portable

Expose concrete execution as a library
-}
module Kore.Exec
    ( exec
    , search
    , prove
    ) where

import qualified Control.Arrow as Arrow
import           Control.Comonad
import           Control.Monad.Trans.Except
                 ( runExceptT )
import qualified Data.Bifunctor as Bifunctor
                 ( first )
import qualified Data.Map.Merge.Strict as Map
import qualified Data.Map.Strict as Map
import           Data.These
                 ( These (..) )

import           Data.Limit
                 ( Limit (..) )
import qualified Data.Limit as Limit
import           Kore.AST.Common
import           Kore.AST.Identifier
import           Kore.AST.MetaOrObject
                 ( Meta, Object (..), asUnified )
import           Kore.AST.Valid
import qualified Kore.Builtin as Builtin
import           Kore.IndexedModule.IndexedModule
                 ( VerifiedModule )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), extractMetadataTools )
import           Kore.OnePath.Verification
                 ( Axiom (Axiom), Claim (Claim), defaultStrategy, verify )
import qualified Kore.OnePath.Verification as Claim
import           Kore.Predicate.Predicate
                 ( pattern PredicateTrue, makeMultipleOrPredicate,
                 makeTruePredicate, unwrapPredicate )
import           Kore.Step.AxiomPatterns
                 ( AxiomPatternAttributes (trusted),
                 EqualityRule (EqualityRule), RewriteRule (RewriteRule),
                 RulePattern (RulePattern), Trusted (..), extractRewriteAxioms,
                 extractRewriteClaims )
import           Kore.Step.AxiomPatterns as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.BaseStep
                 ( StepProof )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..), toMLPattern )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.ExpandedPattern as Predicated
import           Kore.Step.Function.Registry
                 ( axiomPatternsToEvaluators, extractFunctionAxioms )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
import           Kore.Step.Pattern
import           Kore.Step.Search
                 ( searchGraph )
import qualified Kore.Step.Search as Search
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier (..),
                 SimplificationProof (..), Simplifier, StepPatternSimplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.Simplification.PredicateSubstitution as PredicateSubstitution
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Step.Step
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )
import qualified Kore.Step.Strategy as Strategy
import           Kore.Substitution.Class
                 ( substitute )
import qualified Kore.Substitution.List as ListSubstitution
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
                 ( Unparse )
import           Kore.Variables.Fresh
                 ( FreshVariable )

-- | Concrete execution
exec
    :: VerifiedModule StepperAttributes AxiomPatternAttributes
    -- ^ The main module
    -> CommonStepPattern Object
    -- ^ The input pattern
    -> Limit Natural
    -- ^ The step limit
    -> ([RewriteRule Object] -> Strategy (Prim (RewriteRule Object)))
    -- ^ The strategy to use for execution; see examples in "Kore.Step.Step"
    -> Simplifier (CommonStepPattern Object)
exec indexedModule purePattern stepLimit strategy =
    setUpConcreteExecution indexedModule purePattern stepLimit strategy execute
  where
    Valid { patternSort } = extract purePattern
    execute
        :: MetadataTools Object StepperAttributes
        -> StepPatternSimplifier Object Variable
        -> PredicateSubstitutionSimplifier Object Simplifier
        -> Strategy.ExecutionGraph
            (CommonExpandedPattern Object, StepProof Object Variable)
        -> Simplifier (CommonStepPattern Object)
    execute _ _ _ executionGraph = do
        let (finalConfig, _) = pickLongest executionGraph
        return (forceSort patternSort $ ExpandedPattern.toMLPattern finalConfig)

-- | Concrete execution search
search
    :: VerifiedModule StepperAttributes AxiomPatternAttributes
    -- ^ The main module
    -> CommonStepPattern Object
    -- ^ The input pattern
    -> Limit Natural
    -- ^ The step limit
    -> ([RewriteRule Object] -> Strategy (Prim (RewriteRule Object)))
    -- ^ The strategy to use for execution; see examples in "Kore.Step.Step"
    -> CommonExpandedPattern Object
    -- ^ The pattern to match during execution
    -> Search.Config
    -- ^ The bound on the number of search matches and the search type
    -> Simplifier (CommonStepPattern Object)
search
    verifiedModule
    purePattern
    stepLimit
    strategy
    searchPattern
    searchConfig
  =
    setUpConcreteExecution verifiedModule purePattern stepLimit strategy execute
  where
    Valid { patternSort } = extract purePattern
    execute metadataTools simplifier substitutionSimplifier executionGraph = do
        let
            match target (config, _proof) =
                Search.matchWith
                    metadataTools
                    substitutionSimplifier
                    simplifier
                    target
                    config
        solutionsLists <-
            searchGraph searchConfig (match searchPattern) executionGraph
        let
            solutions =
                concatMap OrOfExpandedPattern.extractPatterns solutionsLists
            orPredicate =
                makeMultipleOrPredicate
                    (Predicated.toPredicate <$> solutions)
        return (forceSort patternSort $ unwrapPredicate orPredicate)

-- | Provide a MetadataTools, simplifier, subsitution simplifier, and execution
-- tree to the callback.
setUpConcreteExecution
    :: VerifiedModule StepperAttributes AxiomPatternAttributes
    -- ^ The main module
    -> CommonStepPattern Object
    -- ^ The input pattern
    -> Limit Natural
    -- ^ The step limit
    -> ([RewriteRule Object] -> Strategy (Prim (RewriteRule Object)))
    -- ^ The strategy to use for execution; see examples in "Kore.Step.Step"
    -> (MetadataTools Object StepperAttributes
        -> StepPatternSimplifier Object Variable
        -> PredicateSubstitutionSimplifier Object Simplifier
        -> Strategy.ExecutionGraph
            (CommonExpandedPattern Object, StepProof Object Variable)
        -> Simplifier a)
    -- ^ Callback to do the execution
    -> Simplifier a
setUpConcreteExecution
    verifiedModule
    purePattern
    stepLimit
    strategy
    execute
  = do
    let metadataTools = extractMetadataTools verifiedModule
    axiomsAndSimplifiers <-
        makeAxiomsAndSimplifiers verifiedModule metadataTools
    let
        (rewriteAxioms, simplifier, substitutionSimplifier) =
            axiomsAndSimplifiers
        runStrategy' pat =
            runStrategy
                (transitionRule metadataTools substitutionSimplifier simplifier)
                (Limit.replicate stepLimit (strategy rewriteAxioms))
                (pat, mempty)
        expandedPattern = makeExpandedPattern purePattern
    (simplifiedPatterns, _) <-
        ExpandedPattern.simplify
            metadataTools substitutionSimplifier simplifier expandedPattern
    let
        initialPattern =
            case OrOfExpandedPattern.extractPatterns simplifiedPatterns of
                [] -> ExpandedPattern.bottomOf patternSort
                (config : _) -> config
          where
            Valid { patternSort } = extract purePattern
    executionGraph <- runStrategy' initialPattern
    execute metadataTools simplifier substitutionSimplifier executionGraph

makeExpandedPattern
    :: CommonStepPattern Object
    -> CommonExpandedPattern Object
makeExpandedPattern pat =
    Predicated
        { term = pat
        , predicate = makeTruePredicate
        , substitution = mempty
        }

preSimplify
    ::  (  CommonStepPattern Object
        -> Simplifier
            (OrOfExpandedPattern Object Variable, SimplificationProof Object)
        )
    -> RulePattern Object
    -> Simplifier (RulePattern Object)
preSimplify
    simplifier
    RulePattern
        { left = lhs
        , right = rhs
        , requires
        , attributes = atts
        }
  = do
    (simplifiedOrLhs, _proof) <- simplifier lhs
    let
        [Predicated {term, predicate = PredicateTrue, substitution}] =
            OrOfExpandedPattern.extractPatterns simplifiedOrLhs
        listSubst =
            ListSubstitution.fromList
                (map (Arrow.first asUnified) (Substitution.unwrap substitution))
    newLhs <- substitute term listSubst
    newRhs <- substitute rhs listSubst
    newRequires <- traverse (`substitute` listSubst) requires
    return RulePattern
        { left = newLhs
        , right = newRhs
        , requires = newRequires
        , attributes = atts
        }

makeAxiomsAndSimplifiers
    :: VerifiedModule StepperAttributes AxiomPatternAttributes
    -> MetadataTools Object StepperAttributes
    -> Simplifier
        ( [RewriteRule Object]
        , StepPatternSimplifier Object Variable
        , PredicateSubstitutionSimplifier Object Simplifier
        )
makeAxiomsAndSimplifiers verifiedModule tools =
    do
        functionAxioms <-
            simplifyFunctionAxioms tools
                (extractFunctionAxioms Object verifiedModule)
        rewriteAxioms <-
            mapM (simplifyRewriteRule tools)
                (extractRewriteAxioms Object verifiedModule)
        let
            functionEvaluators =
                axiomPatternsToEvaluators functionAxioms
            functionRegistry =
                Map.merge
                    (Map.mapMissing (const This))
                    (Map.mapMissing (const That))
                    (Map.zipWithMatched (const These))
                    -- builtin functions
                    (Builtin.koreEvaluators verifiedModule)
                    -- user-defined functions
                    functionEvaluators
            simplifier
                ::  ( SortedVariable variable
                    , Ord (variable Meta)
                    , Ord (variable Object)
                    , Show (variable Meta)
                    , Show (variable Object)
                    , Unparse (variable Object)
                    , FreshVariable variable
                    )
                => StepPatternSimplifier Object variable
            simplifier = Simplifier.create tools functionRegistry
            substitutionSimplifier
                :: PredicateSubstitutionSimplifier Object Simplifier
            substitutionSimplifier =
                PredicateSubstitution.create tools simplifier
        return (rewriteAxioms, simplifier, substitutionSimplifier)

simplifyFunctionAxioms
    :: MetadataTools Object StepperAttributes
    -> Map.Map (Id Object) [EqualityRule Object]
    -> Simplifier (Map.Map (Id Object) [EqualityRule Object])
simplifyFunctionAxioms tools = mapM (mapM simplifyEqualityRule)
  where
    simplifyEqualityRule (EqualityRule rule) =
        EqualityRule <$> preSimplify (emptyPatternSimplifier tools) rule

simplifyRewriteRule
    :: MetadataTools Object StepperAttributes
    -> RewriteRule Object
    -> Simplifier (RewriteRule Object)
simplifyRewriteRule tools (RewriteRule rule) =
    RewriteRule <$> preSimplify (emptyPatternSimplifier tools) rule

emptyPatternSimplifier
    :: MetadataTools Object StepperAttributes
    -> CommonStepPattern Object
    -> Simplifier
        (OrOfExpandedPattern Object Variable, SimplificationProof Object)
emptyPatternSimplifier tools =
    ExpandedPattern.simplify
        tools
        emptySubstitutionSimplifier
        emptySimplifier
    . makeExpandedPattern
  where
    emptySimplifier
        ::  ( SortedVariable variable
            , Ord (variable Meta)
            , Ord (variable Object)
            , Show (variable Meta)
            , Show (variable Object)
            , Unparse (variable Object)
            , FreshVariable variable
            )
        => StepPatternSimplifier Object variable
    emptySimplifier = Simplifier.create tools Map.empty
    emptySubstitutionSimplifier =
        PredicateSubstitution.create tools emptySimplifier


-- | Proving a spec given as a module containing rules to be proven
prove
    :: Limit Natural
    -> VerifiedModule StepperAttributes AxiomPatternAttributes
    -- ^ The main module
    -> VerifiedModule StepperAttributes AxiomPatternAttributes
    -- ^ The spec module
    -> Simplifier (Either (CommonStepPattern Object) ())
prove limit definitionModule specModule = do
    let
        tools = extractMetadataTools definitionModule
    axiomsAndSimplifiers <-
        makeAxiomsAndSimplifiers definitionModule tools
    let
        (rewriteAxioms, simplifier, substitutionSimplifier) =
            axiomsAndSimplifiers
    specAxioms <-
        mapM (sequence . fmap (simplifyRewriteRule tools))
            (extractRewriteClaims Object specModule)
    let
        axioms = fmap Axiom rewriteAxioms
        claims = fmap makeClaim specAxioms

    result <- runExceptT
        $ verify
            tools
            simplifier
            substitutionSimplifier
            (defaultStrategy claims axioms)
            (map (\x -> (x,limit)) (extractUntrustedClaims claims))

    return $ Bifunctor.first toMLPattern result

  where
    makeClaim (attributes, rule) = Claim { rule , attributes }
    extractUntrustedClaims =
        map Claim.rule . filter (not . isTrusted . trusted . Claim.attributes)
