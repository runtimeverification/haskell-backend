{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

Direct interface to rule application (step-wise execution).
See "Kore.Step" for the high-level strategy-based interface.

 -}

module Kore.Step.Step
    ( OrStepResult (..)
    , RulePattern
    , StepResult (..)
    , UnificationProcedure (..)
    --
    , UnifiedRule
    , unifyRule
    , applyUnifiedRule
    , applyRule
    , applyRules
    , applyRewriteRule
    , applyRewriteRules
    , sequenceRules
    , sequenceRewriteRules
    , toConfigurationVariables
    , toAxiomVariables
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import qualified Control.Monad as Monad
import           Control.Monad.Except
import qualified Control.Monad.Morph as Monad.Morph
import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Foldable as Foldable
import qualified Data.Map.Strict as Map
import           Data.Semigroup
                 ( Semigroup (..) )
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.Logger as Log
import           Kore.Predicate.Predicate
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.AxiomPatterns
                 ( RewriteRule (..), RulePattern (RulePattern) )
import qualified Kore.Step.AxiomPatterns as RulePattern
import           Kore.Step.Error
import           Kore.Step.Pattern as Pattern
import           Kore.Step.Representation.ExpandedPattern
                 ( ExpandedPattern )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import           Kore.Step.Representation.MultiAnd
                 ( MultiAnd )
import qualified Kore.Step.Representation.MultiAnd as MultiAnd
import           Kore.Step.Representation.MultiOr
                 ( MultiOr )
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern, OrOfPredicateSubstitution )
import           Kore.Step.Representation.Predicated
                 ( Predicated (Predicated) )
import qualified Kore.Step.Representation.Predicated as Predicated
import           Kore.Step.Representation.PredicateSubstitution
                 ( PredicateSubstitution )
import qualified Kore.Step.Representation.PredicateSubstitution as PredicateSubstitution
import           Kore.Step.Simplification.Data
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Step.Substitution as Substitution
import           Kore.Unification.Data
                 ( UnificationProof )
import           Kore.Unification.Error
                 ( UnificationOrSubstitutionError )
import qualified Kore.Unification.Procedure as Unification
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Fresh
import           Kore.Variables.Target
                 ( Target )
import qualified Kore.Variables.Target as Target

{-| The result of applying an axiom to a pattern. Contains the rewritten
pattern (if any) and the unrewritten part of the original pattern.
-}
data StepResult level variable =
    StepResult
        { rewrittenPattern :: !(ExpandedPattern level variable)
        -- ^ The result of rewritting the pattern
        , remainder :: !(ExpandedPattern level variable)
        -- ^ The unrewritten part of the original pattern
        }
    deriving (Eq, Show)

{-| The result of applying an axiom to a pattern, as an Or.

Contains the rewritten pattern (if any) and the unrewritten part of the
original pattern.
-}
data OrStepResult level variable =
    OrStepResult
        { rewrittenPattern :: !(OrOfExpandedPattern level variable)
        -- ^ The result of rewritting the pattern
        , remainder :: !(OrOfExpandedPattern level variable)
        -- ^ The unrewritten part of the original pattern
        }
    deriving (Eq, Show)

instance Semigroup (OrStepResult level variable) where
    (<>)
        OrStepResult
            { rewrittenPattern = rewrittenPattern1
            , remainder = remainder1
            }
        OrStepResult
            { rewrittenPattern = rewrittenPattern2
            , remainder = remainder2
            }
      =
        OrStepResult
            { rewrittenPattern = rewrittenPattern1 <> rewrittenPattern2
            , remainder = remainder1 <> remainder2
            }
    {-# INLINE (<>) #-}

instance Monoid (OrStepResult level variable) where
    mappend = (<>)
    {-# INLINE mappend #-}

    mempty = OrStepResult { rewrittenPattern = mempty, remainder = mempty }
    {-# INLINE mempty #-}

-- | Wraps functions such as 'unificationProcedure' and
-- 'Kore.Step.Axiom.Matcher.matchAsUnification' to be used in
-- 'stepWithRule'.
newtype UnificationProcedure level =
    UnificationProcedure
        ( forall variable
        .   ( SortedVariable variable
            , Ord (variable level)
            , Show (variable level)
            , Unparse (variable level)
            , OrdMetaOrObject variable
            , ShowMetaOrObject variable
            , MetaOrObject level
            , FreshVariable variable
            )
        => MetadataTools level StepperAttributes
        -> PredicateSubstitutionSimplifier level
        -> StepPatternSimplifier level
        -> BuiltinAndAxiomSimplifierMap level
        -> StepPattern level variable
        -> StepPattern level variable
        -> ExceptT
            (UnificationOrSubstitutionError level variable)
            Simplifier
            ( OrOfPredicateSubstitution level variable
            , UnificationProof level variable
            )
        )

unwrapStepErrorVariables
    :: Functor m
    => ExceptT (StepError level (Target variable)) m a
    -> ExceptT (StepError level                  variable ) m a
unwrapStepErrorVariables =
    withExceptT (mapStepErrorVariables Target.unwrapVariable)

unwrapPatternVariables
    ::  forall variable
    .   ( Ord     (variable Object)
        , Unparse (variable Object)
        )
    => StepPattern Object (Target variable)
    -> StepPattern Object variable
unwrapPatternVariables = Pattern.mapVariables Target.unwrapVariable

unwrapPredicateVariables
    ::  forall variable
    .   ( Ord     (variable Object)
        , Unparse (variable Object)
        )
    => Predicate Object (Target variable)
    -> Predicate Object variable
unwrapPredicateVariables = fmap unwrapPatternVariables

{- | Remove axiom variables from the substitution and unwrap all variables.
 -}
unwrapConfiguration
    :: Ord (variable level)
    => ExpandedPattern level (Target variable)
    -> ExpandedPattern level variable
unwrapConfiguration config@Predicated { substitution } =
    ExpandedPattern.mapVariables Target.unwrapVariable
        config { ExpandedPattern.substitution = substitution' }
  where
    substitution' = Substitution.filter Target.isNonTarget substitution

unwrapRemainder
    :: (Ord (variable Object), Unparse (variable Object))
    => Predicate Object (Target variable)
    -> Predicate Object variable
unwrapRemainder remainder
  | hasFreeAxiomVariables =
    (error . show . Pretty.vsep)
        [ "Unexpected free axiom variables:"
        , (Pretty.indent 4 . Pretty.sep)
            (unparse <$> Foldable.toList freeAxiomVariables)
        , "in remainder:"
        , Pretty.indent 4 (unparse remainder)
        ]
  | otherwise =
    unwrapPredicateVariables remainder
  where
    freeAxiomVariables =
        Set.filter Target.isTarget (Predicate.freeVariables remainder)
    hasFreeAxiomVariables = not (Set.null freeAxiomVariables)

wrapUnificationOrSubstitutionError
    :: Functor m
    => ExceptT (UnificationOrSubstitutionError level variable) m a
    -> ExceptT (StepError                      level variable) m a
wrapUnificationOrSubstitutionError =
    withExceptT unificationOrSubstitutionToStepError

{- | Lift an action from the unifier into the stepper.
 -}
liftFromUnification
    :: Monad m
    => BranchT (ExceptT (UnificationOrSubstitutionError level variable) m) a
    -> BranchT (ExceptT (StepError level variable                     ) m) a
liftFromUnification = Monad.Morph.hoist wrapUnificationOrSubstitutionError

{- | A @UnifiedRule@ has been renamed and unified with a configuration.

The rule's 'RulePattern.requires' clause is combined with the unification
solution and the renamed rule is wrapped with the combined condition.

 -}
type UnifiedRule variable =
    Predicated Object variable (RulePattern Object variable)

{- | Attempt to unify a rule with the initial configuration.

The rule variables are renamed to avoid collision with the configuration. The
rule's 'RulePattern.requires' clause is combined with the unification
solution. The combined condition is simplified and checked for
satisfiability.

If any of these steps produces an error, then @unifyRule@ returns that error.

@unifyRule@ returns the renamed rule wrapped with the combined conditions on
unification. The substitution is not applied to the renamed rule.

 -}
unifyRule
    ::  forall variable
    .   ( Ord     (variable Object)
        , Show    (variable Object)
        , Unparse (variable Object)
        , FreshVariable  variable
        , SortedVariable variable
        )
    => MetadataTools Object StepperAttributes
    -> UnificationProcedure Object
    -> PredicateSubstitutionSimplifier Object
    -> StepPatternSimplifier Object
    -> BuiltinAndAxiomSimplifierMap Object

    -> ExpandedPattern Object variable
    -- ^ Initial configuration
    -> RulePattern Object variable
    -- ^ Rule
    -> BranchT
        (ExceptT (StepError Object variable) Simplifier)
        (UnifiedRule variable)
unifyRule
    metadataTools
    (UnificationProcedure unificationProcedure)
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers

    initial@Predicated { term = initialTerm }
    rule
  = do
    -- Rename free axiom variables to avoid free variables from the initial
    -- configuration.
    let
        configVariables = ExpandedPattern.freeVariables initial
        (_, rule') = RulePattern.refreshRulePattern configVariables rule
    -- Unify the left-hand side of the rule with the term of the initial
    -- configuration.
    let
        RulePattern { left = ruleLeft } = rule'
    unification <- unifyPatterns ruleLeft initialTerm
    -- Combine the unification solution with the rule's requirement clause.
    let
        RulePattern { requires = ruleRequires } = rule'
        requires' = PredicateSubstitution.fromPredicate ruleRequires
    unification' <- normalize (unification <> requires')
    return (rule' `Predicated.withCondition` unification')
  where
    unifyPatterns
        :: StepPattern Object variable
        -> StepPattern Object variable
        -> BranchT
            (ExceptT (StepError Object variable) Simplifier)
            (PredicateSubstitution Object variable)
    unifyPatterns pat1 pat2 = do
        (unifiers, _) <-
            liftFromUnification
            $ Monad.Trans.lift
            $ unificationProcedure
                metadataTools
                predicateSimplifier
                patternSimplifier
                axiomSimplifiers
                pat1
                pat2
        scatter unifiers
    normalize
        :: PredicateSubstitution Object variable
        -> BranchT
            (ExceptT (StepError Object variable) Simplifier)
            (PredicateSubstitution Object variable)
    normalize =
        liftFromUnification
        . Substitution.normalizeExcept
            metadataTools
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers

{- | Apply a rule to produce final configurations given some initial conditions.

The initial conditions are merged with any conditions from the rule unification
and normalized.

 -}
applyUnifiedRule
    ::  forall variable
    .   ( Ord     (variable Object)
        , Show    (variable Object)
        , Unparse (variable Object)
        , FreshVariable  variable
        , SortedVariable variable
        )
    => MetadataTools Object StepperAttributes
    -> PredicateSubstitutionSimplifier Object
    -> StepPatternSimplifier Object
    -> BuiltinAndAxiomSimplifierMap Object

    -> PredicateSubstitution Object variable
    -- ^ Initial conditions
    -> UnifiedRule variable
    -- ^ Non-normalized final configuration
    -> BranchT
        (ExceptT (StepError Object variable) Simplifier)
        (ExpandedPattern Object variable)
applyUnifiedRule
    metadataTools
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers

    initial
    unifiedRule
  = do
    -- Combine the initial conditions, the unification conditions, and the axiom
    -- ensures clause. The axiom requires clause is included by unifyRule.
    let
        Predicated { term = renamedRule } = unifiedRule
        RulePattern { ensures } = renamedRule
        ensuresCondition = PredicateSubstitution.fromPredicate ensures
        unification = Predicated.withoutTerm unifiedRule
    finalCondition <- normalize (initial <> unification <> ensuresCondition)
    -- Apply the normalized substitution to the right-hand side of the axiom.
    let
        Predicated { substitution } = finalCondition
        substitution' = Substitution.toMap substitution
        RulePattern { right = finalTerm } = renamedRule
        finalTerm' = Pattern.substitute substitution' finalTerm
    return finalCondition { ExpandedPattern.term = finalTerm' }
  where
    normalize
        :: PredicateSubstitution Object variable
        -> BranchT
            (ExceptT (StepError Object variable) Simplifier)
            (PredicateSubstitution Object variable)
    normalize =
        liftFromUnification
        . Substitution.normalizeExcept
            metadataTools
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers

{- | Apply the remainder predicate to the given initial configuration.

 -}
applyRemainder
    ::  forall variable
    .   ( Ord     (variable Object)
        , Show    (variable Object)
        , Unparse (variable Object)
        , FreshVariable  variable
        , SortedVariable variable
        )
    => MetadataTools Object StepperAttributes
    -> PredicateSubstitutionSimplifier Object
    -> StepPatternSimplifier Object
    -> BuiltinAndAxiomSimplifierMap Object

    -> ExpandedPattern Object variable
    -- ^ Initial configuration
    -> Predicate Object variable
    -- ^ Remainder
    -> BranchT
        (ExceptT (StepError Object variable) Simplifier)
        (ExpandedPattern Object variable)
applyRemainder
    metadataTools
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers

    initial
    (PredicateSubstitution.fromPredicate -> remainder)
  = do
    let final = initial `Predicated.andCondition` remainder
        finalCondition = Predicated.withoutTerm final
        Predicated { Predicated.term = finalTerm } = final
    normalizedCondition <- normalize finalCondition
    return normalizedCondition { Predicated.term = finalTerm }
  where
    normalize
        :: PredicateSubstitution Object variable
        -> BranchT
            (ExceptT (StepError Object variable) Simplifier)
            (PredicateSubstitution Object variable)
    normalize =
        liftFromUnification
        . Substitution.normalizeExcept
            metadataTools
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers

toAxiomVariables
    :: Ord (variable level)
    => RulePattern level variable
    -> RulePattern level (Target variable)
toAxiomVariables = RulePattern.mapVariables Target.Target

toConfigurationVariables
    :: Ord (variable level)
    => ExpandedPattern level variable
    -> ExpandedPattern level (Target variable)
toConfigurationVariables = ExpandedPattern.mapVariables Target.NonTarget

data Result variable =
    Result
        { unifiedRule :: !(UnifiedRule (Target variable))
        , result      :: !(ExpandedPattern Object variable)
        }

{- | Fully apply a single rule to the initial configuration.

The rule is applied to the initial configuration to produce zero or more final
configurations.

 -}
applyRule
    ::  ( Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        , FreshVariable variable
        , SortedVariable variable
        )
    => MetadataTools Object StepperAttributes
    -> PredicateSubstitutionSimplifier Object
    -> StepPatternSimplifier Object
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from symbol IDs to defined functions
    -> UnificationProcedure Object

    -> ExpandedPattern Object variable
    -- ^ Configuration being rewritten.
    -> RulePattern Object variable
    -- ^ Rewriting axiom
    -> ExceptT (StepError Object variable) Simplifier
        (MultiOr (Result variable))
applyRule
    metadataTools
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers
    unificationProcedure

    initial
    rule
  = Log.withLogScope "applyRule"
    $ unwrapStepErrorVariables
    $ do
        let
            -- Wrap the rule and configuration so that unification prefers to
            -- substitute axiom variables.
            initial' = toConfigurationVariables initial
            rule' = toAxiomVariables rule
        gather $ do
            unifiedRule <- unifyRule' initial' rule'
            let initialCondition = Predicated.withoutTerm initial'
            final <- applyUnifiedRule' initialCondition unifiedRule
            result <- checkSubstitutionCoverage initial' unifiedRule final
            return Result { unifiedRule, result }
  where
    unifyRule' =
        unifyRule
            metadataTools
            unificationProcedure
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers
    applyUnifiedRule' =
        applyUnifiedRule
            metadataTools
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers

{- | Fully apply a single rewrite rule to the initial configuration.

The rewrite rule is applied to the initial configuration to produce zero or more
final configurations.

 -}
applyRewriteRule
    ::  ( Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        , FreshVariable variable
        , SortedVariable variable
        )
    => MetadataTools Object StepperAttributes
    -> PredicateSubstitutionSimplifier Object
    -> StepPatternSimplifier Object
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from symbol IDs to defined functions
    -> UnificationProcedure Object

    -> ExpandedPattern Object variable
    -- ^ Configuration being rewritten.
    -> RewriteRule Object variable
    -- ^ Rewriting axiom
    -> ExceptT (StepError Object variable) Simplifier
        (MultiOr (Result variable))
applyRewriteRule
    metadataTools
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers
    unificationProcedure

    initial
    (RewriteRule rule)
  = Log.withLogScope "applyRewriteRule"
    $ applyRule
        metadataTools
        predicateSimplifier
        patternSimplifier
        axiomSimplifiers
        unificationProcedure
        initial
        rule

{- | Check that the final substitution covers the applied rule appropriately.

The final substitution should cover all the free variables on the left-hand side
of the applied rule; otherwise, we would wrongly introduce
universally-quantified variables into the final configuration. Failure of the
coverage check indicates a problem with unification, so in that case
@checkSubstitutionCoverage@ throws an error message with the axiom and the
initial and final configurations.

@checkSubstitutionCoverage@ calls @unwrapVariables@ to remove the axiom
variables from the substitution and unwrap all the 'Target's; this is
safe because we have already checked that all the universally-quantified axiom
variables have been instantiated by the substitution.

 -}
checkSubstitutionCoverage
    ::  ( MetaOrObject level
        , Monad m
        , SortedVariable variable
        , Ord     (variable level)
        , Show    (variable level)
        , Unparse (variable level)
        )
    => ExpandedPattern level (Target variable)
    -- ^ Initial configuration
    -> UnifiedRule (Target variable)
    -- ^ Unified rule
    -> ExpandedPattern level (Target variable)
    -- ^ Configuration after applying rule
    -> m (ExpandedPattern level variable)
checkSubstitutionCoverage initial unified final = do
    (Monad.unless checkPass . error . show . Pretty.vsep)
        [ "While applying axiom:"
        , Pretty.indent 4 (Pretty.pretty axiom)
        , "from the initial configuration:"
        , Pretty.indent 4 (unparse initial)
        , "to the final configuration:"
        , Pretty.indent 4 (unparse final)
        , "Failed substitution coverage check!"
        , "Expected substitution to cover all variables:"
        , (Pretty.indent 4 . Pretty.sep)
            (unparse <$> Set.toAscList leftAxiomVariables)
        , "in the left-hand side of the axiom."
        ]
    return (unwrapConfiguration final)
  where
    checkPass = isCoveringSubstitution || isInitialSymbolic
    Predicated { term = axiom } = unified
    leftAxiomVariables =
        Pattern.freeVariables leftAxiom
      where
        RulePattern { left = leftAxiom } = axiom
    Predicated { substitution } = final
    substitutionVariables = Map.keysSet (Substitution.toMap substitution)
    isCoveringSubstitution =
        Set.isSubsetOf leftAxiomVariables substitutionVariables
    isInitialSymbolic =
        (not . Foldable.any Target.isNonTarget) substitutionVariables

{- | Negate the disjunction of unification solutions to form the /remainders/.

The /remainders/ are the parts of the initial configuration that are not matched
by any applied rule.

 -}
negateUnification
    ::  ( Ord     (variable Object)
        , Show    (variable Object)
        , Unparse (variable Object)
        , SortedVariable variable
        )
    => MultiOr (PredicateSubstitution Object (Target variable))
    -> MultiOr (Predicate Object variable)
negateUnification =
    fmap unwrapRemainder
    . foldr negateUnification1 top
    . Foldable.toList
  where
    top = pure Predicate.makeTruePredicate
    negateUnification1 unification negations =
        Predicate.makeAndPredicate
            <$> mkNotMultiAnd conditions
            <*> negations
      where
        conditions = unificationConditions unification

mkNotMultiAnd
    ::  ( Ord     (variable Object)
        , Show    (variable Object)
        , Unparse (variable Object)
        , SortedVariable variable
        )
    => MultiAnd (Predicate Object variable)
    -> MultiOr  (Predicate Object variable)
mkNotMultiAnd = MultiOr.make . map Predicate.makeNotPredicate . Foldable.toList

mkNotMultiOr
    ::  ( Ord     (variable Object)
        , Show    (variable Object)
        , Unparse (variable Object)
        , SortedVariable variable
        )
    => MultiOr  (Predicate Object variable)
    -> MultiAnd (Predicate Object variable)
mkNotMultiOr = MultiAnd.make . map Predicate.makeNotPredicate . Foldable.toList

mkMultiAndPredicate
    ::  ( Ord     (variable Object)
        , Show    (variable Object)
        , Unparse (variable Object)
        , SortedVariable variable
        )
    => MultiAnd (Predicate Object variable)
    ->           Predicate Object variable
mkMultiAndPredicate = Predicate.makeMultipleAndPredicate . Foldable.toList

{- | Represent the unification solution as a conjunction of predicates.
 -}
unificationConditions
    ::  ( Ord     (variable Object)
        , Show    (variable Object)
        , Unparse (variable Object)
        , SortedVariable variable
        )
    => PredicateSubstitution Object (Target variable)
    -- ^ Unification solution
    -> MultiAnd (Predicate Object (Target variable))
unificationConditions Predicated { predicate, substitution } =
    pure predicate <|> substitutionConditions substitution'
  where
    substitution' = Substitution.filter Target.isNonTarget substitution

substitutionConditions
    ::  ( Ord     (variable Object)
        , Show    (variable Object)
        , Unparse (variable Object)
        , SortedVariable variable
        )
    => Substitution Object variable
    -> MultiAnd (Predicate Object variable)
substitutionConditions subst =
    MultiAnd.make (substitutionCoverageWorker <$> Substitution.unwrap subst)
  where
    substitutionCoverageWorker (x, t) =
        Predicate.makeEqualsPredicate (mkVar x) t

{- | Apply the given rules to the initial configuration in parallel.

See also: 'applyRewriteRule'

 -}
applyRules
    ::  forall variable
    .   ( Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        , FreshVariable variable
        , SortedVariable variable
        )
    => MetadataTools Object StepperAttributes
    -> PredicateSubstitutionSimplifier Object
    -> StepPatternSimplifier Object
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from symbol IDs to defined functions
    -> UnificationProcedure Object

    -> [RulePattern Object variable]
    -- ^ Rewrite rules
    -> ExpandedPattern Object variable
    -- ^ Configuration being rewritten
    -> ExceptT (StepError Object variable) Simplifier
        (OrStepResult Object variable)
applyRules
    metadataTools
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers
    unificationProcedure

    rules
    initial
  = do
    results <- Foldable.fold <$> traverse applyRule' rules
    let unifications = Predicated.withoutTerm . unifiedRule <$> results
    remainder <- gather $ do
        remainder <- scatter (negateUnification unifications)
        applyRemainder' initial remainder
    let rewrittenPattern = result <$> results
    return OrStepResult { rewrittenPattern, remainder }
  where
    applyRule' =
        applyRule
            metadataTools
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers
            unificationProcedure
            initial
    applyRemainder' =
        applyRemainder
            metadataTools
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers

{- | Apply the given rewrite rules to the initial configuration in parallel.

See also: 'applyRewriteRule'

 -}
applyRewriteRules
    ::  forall variable
    .   ( Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        , FreshVariable variable
        , SortedVariable variable
        )
    => MetadataTools Object StepperAttributes
    -> PredicateSubstitutionSimplifier Object
    -> StepPatternSimplifier Object
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from symbol IDs to defined functions

    -> [RewriteRule Object variable]
    -- ^ Rewrite rules
    -> ExpandedPattern Object variable
    -- ^ Configuration being rewritten
    -> ExceptT (StepError Object variable) Simplifier
        (OrStepResult Object variable)
applyRewriteRules
    metadataTools
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers

    rewriteRules
  =
    applyRules
        metadataTools
        predicateSimplifier
        patternSimplifier
        axiomSimplifiers
        (UnificationProcedure Unification.unificationProcedure)
        (getRewriteRule <$> rewriteRules)

{- | Apply the given rewrite rules to the initial configuration in sequence.

See also: 'applyRewriteRule'

 -}
sequenceRules
    ::  forall variable
    .   ( Ord     (variable Object)
        , Show    (variable Object)
        , Unparse (variable Object)
        , FreshVariable  variable
        , SortedVariable variable
        )
    => MetadataTools Object StepperAttributes
    -> PredicateSubstitutionSimplifier Object
    -> StepPatternSimplifier Object
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from symbol IDs to defined functions
    -> UnificationProcedure Object

    -> ExpandedPattern Object variable
    -- ^ Configuration being rewritten
    -> [RulePattern Object variable]
    -- ^ Rewrite rules
    -> ExceptT (StepError Object variable) Simplifier
        (OrStepResult Object variable)
sequenceRules
    metadataTools
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers
    unificationProcedure
    initialConfig
  =
    sequenceRulesWorker empty (pure initialConfig)
  where
    -- The single remainder of the input configuration after rewriting to
    -- produce the disjunction of results.
    remainingAfter
        :: ExpandedPattern Object variable
        -- ^ initial configuration
        -> MultiOr (Result variable)
        -- ^ disjunction of results
        -> ExpandedPattern Object variable
    remainingAfter config results =
        let covered =
                mkMultiAndPredicate
                . unificationConditions
                . Predicated.withoutTerm
                . unifiedRule
                <$> results
            notCovered =
                PredicateSubstitution.fromPredicate
                $ unwrapRemainder
                $ mkMultiAndPredicate
                $ mkNotMultiOr covered
        in config `Predicated.andCondition` notCovered

    sequenceRulesWorker done pending [] =
        return OrStepResult
            { rewrittenPattern = done
            , remainder = pending
            }

    sequenceRulesWorker done pending (rule : rules) = do
        results <- traverse applyRule' pending
        let finals = MultiOr.filterOr (fst <$> results)
            done' = done <> Foldable.fold finals
            pending' = MultiOr.filterOr (snd <$> results)
        sequenceRulesWorker done' pending' rules
      where
        -- Apply rule to produce a pair of the rewritten patterns and
        -- single remainder configuration.
        applyRule' config = do
            results <-
                applyRule
                    metadataTools
                    predicateSimplifier
                    patternSimplifier
                    axiomSimplifiers
                    unificationProcedure
                    config
                    rule
            let pending' = remainingAfter config results
            return (result <$> results, pending')

{- | Apply the given rewrite rules to the initial configuration in sequence.

See also: 'applyRewriteRule'

 -}
sequenceRewriteRules
    ::  forall variable
    .   ( Ord     (variable Object)
        , Show    (variable Object)
        , Unparse (variable Object)
        , FreshVariable  variable
        , SortedVariable variable
        )
    => MetadataTools Object StepperAttributes
    -> PredicateSubstitutionSimplifier Object
    -> StepPatternSimplifier Object
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from symbol IDs to defined functions

    -> ExpandedPattern Object variable
    -- ^ Configuration being rewritten
    -> [RewriteRule Object variable]
    -- ^ Rewrite rules
    -> ExceptT (StepError Object variable) Simplifier
        (OrStepResult Object variable)
sequenceRewriteRules
    metadataTools
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers
    initialConfig
    rewriteRules
  =
    sequenceRules
        metadataTools
        predicateSimplifier
        patternSimplifier
        axiomSimplifiers
        (UnificationProcedure Unification.unificationProcedure)
        initialConfig
        (getRewriteRule <$> rewriteRules)
