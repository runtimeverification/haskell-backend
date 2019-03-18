{-|
Module      : Kore.Step.BaseStep
Description : Single step execution
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.BaseStep
    ( OrStepResult (..)
    , RulePattern
    , StepperConfiguration (..)
    , StepResult (..)
    , StepperVariable (..)
    , StepProof (..)
    , StepProofAtom (..)
    , UnificationProcedure (..)
    , VariableRenaming (..)
    , simplificationProof
    , stepProof
    , stepProofSumName
    , stepWithRemainders
    , stepWithRemaindersForUnifier
    , stepWithRewriteRule
    , stepWithRule
    --
    , unifyRule
    , instantiateRule
    , applyRule
    ) where

import           Control.Monad.Except
import qualified Control.Monad.Morph as Monad.Morph
import qualified Control.Monad.Trans as Monad.Trans
import           Control.Monad.Trans.Except
                 ( throwE )
import qualified Data.Hashable as Hashable
import           Data.List
                 ( foldl' )
import qualified Data.Map.Strict as Map
import           Data.Maybe
                 ( mapMaybe )
import           Data.Semigroup
                 ( Semigroup (..) )
import           Data.Sequence
                 ( Seq )
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as Text
import           GHC.Generics
                 ( Generic )

import qualified Kore.Annotation.Valid as Valid
import qualified Kore.AST.Common as Common
import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Debug
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.Logger as Log
import           Kore.Predicate.Predicate
                 ( Predicate, makeAndPredicate, makeNotPredicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.AxiomPatterns
                 ( RewriteRule (RewriteRule), RulePattern (..) )
import qualified Kore.Step.AxiomPatterns as RulePattern
import           Kore.Step.Error
import           Kore.Step.Pattern as Pattern
import           Kore.Step.Representation.ExpandedPattern
                 ( ExpandedPattern )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( extractPatterns, make, merge, mergeAll )
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern, OrOfPredicateSubstitution )
import           Kore.Step.Representation.PredicateSubstitution
                 ( PredicateSubstitution, Predicated (..) )
import qualified Kore.Step.Representation.PredicateSubstitution as PredicateSubstitution
import           Kore.Step.Simplification.Data
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutionsExcept )
import qualified Kore.Step.Substitution as Substitution
import           Kore.Unification.Data
                 ( UnificationProof (..) )
import qualified Kore.Unification.Data as Unification.Proof
import           Kore.Unification.Error
                 ( UnificationError (..), UnificationOrSubstitutionError )
import qualified Kore.Unification.Procedure as Unification
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Fresh

{-| 'StepperConfiguration' represents the configuration to which a rewriting
axiom is applied.

A configuration consists of a pattern and a condition predicate, and would be
represented as pattern /\ condition-predicate in Kore.
--}
data StepperConfiguration level = StepperConfiguration
    { stepperConfigurationPattern       :: !(CommonStepPattern level)
    -- ^ The pattern being rewritten.

    , stepperConfigurationCondition     :: !(CommonStepPattern level)
    -- ^ The condition predicate.
    -- TODO(virgil): Make this an EvaluatedCondition.
    }
    deriving (Show, Eq)

{- | 'StepProof' is the proof for an execution step or steps.
 -}
newtype StepProof (level :: *) (variable :: * -> *) =
    StepProof { getStepProof :: Seq (StepProofAtom level variable) }
  deriving (Eq, Show)

instance Hashable.Hashable (StepProof level variable) where
    hashWithSalt s _ = Hashable.hashWithSalt s (0 :: Int)

instance Semigroup (StepProof level variable) where
    (<>) (StepProof a) (StepProof b) = StepProof (a <> b)

instance Monoid (StepProof level variable) where
    mempty = StepProof mempty
    mappend = (<>)

stepProof :: StepProofAtom level variable -> StepProof level variable
stepProof atom = StepProof (Seq.singleton atom)

simplificationProof :: SimplificationProof level -> StepProof level variable
simplificationProof = stepProof . StepProofSimplification

{- | The smallest unit of a 'StepProof'.

  @StepProofAtom@ encapsulates the separate proofs resulting from unification,
  variable renaming, and simplification.

 -}
data StepProofAtom (level :: *) (variable :: * -> *)
    = StepProofUnification !(UnificationProof level variable)
    -- ^ Proof for a unification that happened during the step.
    | StepProofVariableRenamings [VariableRenaming level variable]
    -- ^ Proof for the remanings that happened during ther proof.
    | StepProofSimplification !(SimplificationProof level)
    -- ^ Proof for the simplification part of a step.
    deriving (Show, Eq, Generic)

{-| 'VariableRenaming' represents a renaming of a variable.
-}
data VariableRenaming level variable = VariableRenaming
    { variableRenamingOriginal :: variable level
    , variableRenamingRenamed  :: variable level
    }
    deriving (Show, Eq)

{- | Distinguish variables by their source (axiom or configuration).

@StepperVariable@ ensures that axiom variables are always 'LT' configuration
variables, so that the unification procedure prefers to generate substitutions
for axiom variables instead of configuration variables.

 -}
data StepperVariable variable level
    = AxiomVariable !(variable level)
    | ConfigurationVariable !(variable level)
    deriving (Show, Ord, Eq)

unwrapStepperVariable :: StepperVariable variable level -> variable level
unwrapStepperVariable (AxiomVariable variable) = variable
unwrapStepperVariable (ConfigurationVariable variable) = variable

instance
    SortedVariable variable
    => SortedVariable (StepperVariable variable)
  where
    sortedVariableSort (AxiomVariable variable) =
        sortedVariableSort variable
    sortedVariableSort (ConfigurationVariable variable) =
        sortedVariableSort variable
    fromVariable = AxiomVariable . fromVariable
    toVariable (AxiomVariable var) = toVariable var
    toVariable (ConfigurationVariable var) = toVariable var

{- | The implementation of @refreshVariable@ for 'StepperVariable' ensures that
fresh variables are always unique under projection by 'unwrapStepperVariable'.
 -}
instance
    (FreshVariable variable, SortedVariable variable) =>
    FreshVariable (StepperVariable variable)
  where
    refreshVariable (Set.map unwrapStepperVariable -> avoiding) =
        \case
            AxiomVariable variable ->
                AxiomVariable <$> refreshVariable avoiding variable
            ConfigurationVariable variable ->
                ConfigurationVariable <$> refreshVariable avoiding variable

instance
    Unparse (variable level) =>
    Unparse (StepperVariable variable level)
  where
    unparse =
        \case
            AxiomVariable var -> "Axiom" <> unparse var
            ConfigurationVariable var -> "Config" <> unparse var

{-! The result of applying an axiom to a pattern. Contains the rewritten
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

{-! The result of applying an axiom to a pattern, as an Or.

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

{-| 'stepProofSumName' extracts the constructor name for a 'StepProof' -}
stepProofSumName :: StepProofAtom variable level -> String
stepProofSumName (StepProofUnification _)       = "StepProofUnification"
stepProofSumName (StepProofVariableRenamings _) = "StepProofVariableRenamings"
stepProofSumName (StepProofSimplification _)    = "StepProofSimplification"

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

{- |
    Use the given axiom to execute a single rewriting step.

    Does not properly handle various cases, among them:
    - sigma(x, y) => y    vs    a

    Returns 'Left' only if there is an error. It is not an error if the axiom
    does not apply to the given configuration.
-}
stepWithRule
    :: forall level variable .
        ( FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , OrdMetaOrObject variable
        , SortedVariable variable
        , Show (variable level)
        , ShowMetaOrObject variable
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> UnificationProcedure level
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from symbol IDs to defined functions
    -> ExpandedPattern level variable
    -- ^ Configuration being rewritten.
    -> RulePattern level variable
    -- ^ Rewriting axiom
    -> ExceptT
        (StepError level variable)
        Simplifier
        [   ( StepResult level variable
            , StepProof level variable
            )
        ]
stepWithRule
    tools
    (UnificationProcedure unificationProcedure')
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    config
    axiom
  = Log.withLogScope "stepWithRule" $ do
    Log.logDebug
        $ "Attempting rule \n"
        <> Text.pack (show axiom)
        <> "\n for \n"
        <> Text.pack (show config)
    let configVariables = ExpandedPattern.freeVariables config
        (renaming, axiom') =
            RulePattern.refreshRulePattern configVariables axiom

        axiom'' = RulePattern.mapVariables AxiomVariable axiom'
        config' = ExpandedPattern.mapVariables ConfigurationVariable config

        RulePattern { left = axiomLeft } = axiom''
        Predicated { term = startPattern } = config'

        -- Remap unification and substitution errors into 'StepError'.
        normalizeUnificationOrSubstitutionError
            ::  ( FreshVariable variable
                , MetaOrObject level
                , Ord (variable level)
                , Show (variable level)
                )
            => ExceptT
                (UnificationOrSubstitutionError
                    level
                    (StepperVariable variable)
                )
                Simplifier
                a
            -> ExceptT (StepError level variable) Simplifier a
        normalizeUnificationOrSubstitutionError action =
            unwrapStepErrorVariables
            $ withExceptT unificationOrSubstitutionToStepError action

    -- Unify the left-hand side of the rewriting axiom with the initial
    -- configuration, producing a substitution (instantiating the axiom to the
    -- configuration) subject to a predicate.
    (unificationSolutions, unificationProof) <-
        normalizeUnificationOrSubstitutionError
            (unificationProcedure'
                tools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                axiomLeft
                startPattern
            )
    let unificationProof' =
            (stepProof . StepProofUnification)
                (Unification.Proof.mapVariables
                    unwrapStepperVariable
                    unificationProof
                )
        renamingProof =
            (stepProof . StepProofVariableRenamings)
                (variablePairToRenaming <$> Map.toList renaming)
          where
            variablePairToRenaming (original, renamed) =
                VariableRenaming
                    { variableRenamingOriginal = original
                    , variableRenamingRenamed  = renamed
                    }
        proof = renamingProof <> unificationProof'
        attachProof result = (result, proof)
    results <-
        traverse
            (applyUnificationToRhs
                tools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                axiom''
                config'
            )
            (MultiOr.extractPatterns unificationSolutions)
    return (attachProof <$> results)

applyUnificationToRhs
    :: forall level variable .
        ( Eq (variable Meta)
        , Eq (variable Object)
        , Eq (variable level)
        , FreshVariable variable
        , MetaOrObject level
        , Ord (variable Meta)
        , Ord (variable Object)
        , Ord (variable level)
        , Show (variable Meta)
        , Show (variable Object)
        , Show (variable level)
        , Unparse (variable level)
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from symbol IDs to defined functions
    -> RulePattern level (StepperVariable variable)
    -- ^ Applied rule
    -> ExpandedPattern level (StepperVariable variable)
    -- ^ Initial configuration
    -> PredicateSubstitution level (StepperVariable variable)
    -- ^ Unification solution
    -> ExceptT
        (StepError level variable)
        Simplifier
        (StepResult level variable)
applyUnificationToRhs
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    axiom@RulePattern
        { left = axiomLeft
        , right = axiomRight
        , requires = axiomRequires
        }
    expandedPattern@Predicated
        {term = initialTerm, substitution = initialSubstitution}
    Predicated
        { predicate = rawPredicate
        , substitution = rawSubstitution
        }
  = do
    let
        Predicated
            { predicate = startCondition
            , substitution = startSubstitution
            } = expandedPattern

    -- Combine the all the predicates and substitutions generated
    -- above and simplify the result.
    ( Predicated
            { predicate = normalizedCondition
            , substitution = normalizedSubstitution
            }
        , _proof
        ) <-
            unwrapStepErrorVariables
            $ withExceptT unificationOrSubstitutionToStepError
            $ mergePredicatesAndSubstitutionsExcept
                tools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                [ startCondition  -- from initial configuration
                , axiomRequires   -- from axiom
                , rawPredicate    -- produced during unification
                ]
                [rawSubstitution, startSubstitution]

    -- Join the axiom predicate and the substitution predicate, together
    -- with the substitution in order to filter the handled values
    -- out of the initial pattern, producing the step reminder.
    ( Predicated
            { term = ()
            , predicate = normalizedRemainderPredicateRaw
            , substitution = normalizedRemainderSubstitution
            }
        , _proof
        ) <-
            unwrapStepErrorVariables
            $ withExceptT unificationOrSubstitutionToStepError
            $ mergePredicatesAndSubstitutionsExcept
                tools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                [ axiomRequires  -- from axiom
                , rawPredicate   -- produced during unification
                ]
                [rawSubstitution]

    let
        negatedRemainder :: Predicate level (StepperVariable variable)
        negatedRemainder =
            (makeNotPredicate . PredicateSubstitution.toPredicate)
                Predicated
                    { term = ()
                    , predicate = normalizedRemainderPredicateRaw
                    , substitution =
                        -- Note that this filtering is reasonable only because
                        -- below we check that there are no axiom variables left
                        -- in the predicate.
                        Substitution.filter isConfigurationVariable
                            normalizedRemainderSubstitution
                    }
        -- the remainder predicate is the start predicate from which we
        -- remove what was handled by the current axiom, i.e. we `and` it with
        -- the negated unification results and the axiom condition.
        normalizedRemainderPredicate
            :: Predicate level (StepperVariable variable)
        normalizedRemainderPredicate =
            makeAndPredicate
                startCondition  -- from initial configuration
                negatedRemainder
        isConfigurationVariable :: StepperVariable variable level -> Bool
        isConfigurationVariable (AxiomVariable _) = False
        isConfigurationVariable (ConfigurationVariable _) = True

    let substitution = Substitution.toMap normalizedSubstitution

        -- Apply substitution to resulting configuration and conditions.
        rawResult = substitute substitution axiomRight

        variablesInLeftAxiom :: Set.Set (variable level)
        variablesInLeftAxiom =
            extractVariables axiomVariableFromStepper
            . Valid.freeVariables
            . extract
            $ axiomLeft
        axiomVariableFromStepper
            :: StepperVariable variable level
            -> Maybe (variable level)
        axiomVariableFromStepper (AxiomVariable v) = Just v
        axiomVariableFromStepper (ConfigurationVariable _) = Nothing
        configVariableFromStepper
            :: StepperVariable variable level
            -> Maybe (variable level)
        configVariableFromStepper (AxiomVariable _) = Nothing
        configVariableFromStepper (ConfigurationVariable v) = Just v
        extractVariables
            :: (StepperVariable variable level -> Maybe (variable level))
            -> Set.Set (StepperVariable variable level)
            -> Set.Set (variable level)
        extractVariables selector =
            Set.fromList . mapMaybe selector . Set.toList
        axiomVarsInSubstitutions :: Set.Set (variable level)
        axiomVarsInSubstitutions = extractVariables axiomVariableFromStepper
            $ Map.keysSet substitution
        configVarsInSubstitutions :: Set.Set (variable level)
        configVarsInSubstitutions = extractVariables configVariableFromStepper
            $ Map.keysSet substitution

    -- Unwrap internal 'StepperVariable's and collect the variable mappings
    -- for the proof.
    result <- unwrapPatternVariables rawResult
    condition <- unwrapPredicateVariables normalizedCondition
    remainderPredicate <- unwrapPredicateVariables normalizedRemainderPredicate

    let isBottom = Predicate.isFalse condition
        allVarsCovered = Set.isSubsetOf
                            variablesInLeftAxiom axiomVarsInSubstitutions
        symbolicPattern = not (Set.null configVarsInSubstitutions)

    when (not (isBottom || allVarsCovered || symbolicPattern))
        $ (error . unlines)
            [ "While applying axiom:", show axiom
            , "to configuration:", show expandedPattern
            , "Unexpected non-false predicate:", show condition
            , "when substitutions:", show axiomVarsInSubstitutions
            , "do not cover all variables in left axiom:"
            , show variablesInLeftAxiom
            ]

    let
        orElse :: a -> a -> a
        p1 `orElse` p2 = if isBottom then p2 else p1
    if not(isBottom) && not(allVarsCovered) && symbolicPattern
    then throwE (StepErrorUnification UnsupportedPatterns)
    else return StepResult
        { rewrittenPattern = Predicated
            { term = result `orElse` mkBottom_
            , predicate = condition
            -- TODO(virgil): Can there be unused variables? Should we
            -- remove them?
            , substitution =
                (Substitution.mapVariables unwrapStepperVariable
                    $ Substitution.filter isConfigurationVariable
                    $ normalizedSubstitution
                )
                `orElse` mempty
            }
        , remainder =
            -- See docs/2019-03-06-Equality-Axiom-Configuration-Splitting.md
            -- for why this works for equality axioms.
            -- See design-decisions/2018-10-24-And-Not-Exists-Simplification.md
            -- for a similar argument for rewrite axioms, but note that it can
            -- be generalized in the same way as the equality axiom document.
            Predicated
                { term = Pattern.mapVariables unwrapStepperVariable initialTerm
                , predicate = remainderPredicate
                , substitution =
                    Substitution.mapVariables
                        unwrapStepperVariable
                        initialSubstitution
                }
        }

-- TODO(virgil): this seems to be used only in tests, consider deleting.
stepWithRewriteRule
    ::  ( FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , OrdMetaOrObject variable
        , SortedVariable variable
        , Show (variable level)
        , ShowMetaOrObject variable
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from symbol IDs to defined functions
    -> ExpandedPattern level variable
    -- ^ Configuration being rewritten.
    -> RewriteRule level variable
    -- ^ Rewriting axiom
    -> ExceptT
        (StepError level variable)
        Simplifier
        [   ( StepResult level variable
            , StepProof level variable
            )
        ]
stepWithRewriteRule
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    patt
    (RewriteRule rule)
  =
    traceExceptT D_BaseStep_stepWithRule [debugArg "rule" rule] $
    Log.withLogScope "stepWithRewriteRule" $
        stepWithRule
                tools
                (UnificationProcedure Unification.unificationProcedure)
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                patt
                rule

{-| Takes a configuration and a set of rules and tries to apply them to the
configuration in order.

The first rule is applied on the entire configuration, while the subsequent
ones are applied on the part of configuration that was not transformed by the
previous ones.

It returns all results from applying these axioms, together with the
untransformed part of the configuration left at the end (if any).

As an example, let us assume that we have the following axioms:

@
a = b if p1
a = c if p2
a = d and p3
@

and we are trying to apply them to 'a'. Then we will get the following results:

@
b and p1
c and (not p1) and p2
d and (not p1) and (not p2) and p3
a and (not p1) and (not p2) and (not p3)
@
-}
stepWithRemaindersForUnifier
    :: forall level variable .
        ( FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , OrdMetaOrObject variable
        , SortedVariable variable
        , Show (variable level)
        , ShowMetaOrObject variable
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> UnificationProcedure level
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from symbol IDs to defined functions
    -> [RulePattern level variable]
    -- ^ Rewriting axiom
    -> ExpandedPattern level variable
    -- ^ Configuration being rewritten.
    -> ExceptT
        (StepError level variable)
        Simplifier
        ( OrStepResult level variable
        , StepProof level variable
        )
stepWithRemaindersForUnifier
    _
    _
    _
    _
    _
    []
    patt
  = return
    ( OrStepResult
        { rewrittenPattern = MultiOr.make []
        , remainder = MultiOr.make [patt]
        }
    , mempty
    )
stepWithRemaindersForUnifier
    tools
    unification
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    (rule : rules)
    patt
  = do
    resultsWithProofs <-
        stepWithRule
            tools
            unification
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            patt
            rule
    let
        (results, proofs) = unzip resultsWithProofs
        rewritten :: [OrOfExpandedPattern level variable]
        remainders ::  [ExpandedPattern level variable]
        (rewritten, remainders) =
            if null results
            then ([], [patt])
            else unzip (map splitStepResult results)
    rewrittenRemaindersWithProofs <-
        mapM
            (stepWithRemaindersForUnifier
                tools
                unification
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                rules
            )
            remainders
    let
        rewrittenRemainders :: [OrStepResult level variable]
        rewrittenRemainderProofs :: [StepProof level variable]
        (rewrittenRemainders, rewrittenRemainderProofs) =
            unzip rewrittenRemaindersWithProofs
        alreadyRewritten :: OrStepResult level variable
        alreadyRewritten =
            OrStepResult
                { rewrittenPattern =
                    MultiOr.mergeAll rewritten
                , remainder = MultiOr.make []
                }
    return
        ( foldl' mergeResults alreadyRewritten rewrittenRemainders
        , mconcat proofs <> mconcat rewrittenRemainderProofs
        )
  where
    mergeResults
        :: OrStepResult level variable
        -> OrStepResult level variable
        -> OrStepResult level variable
    mergeResults
        OrStepResult
            { rewrittenPattern = firstPattern
            , remainder = firstRemainder
            }
        OrStepResult
            { rewrittenPattern = secondPattern
            , remainder = secondRemainder
            }
      =
        OrStepResult
            { rewrittenPattern =
                MultiOr.merge firstPattern secondPattern
            , remainder =
                MultiOr.merge firstRemainder secondRemainder
            }
    splitStepResult
        :: StepResult level variable
        ->  ( OrOfExpandedPattern level variable
            , ExpandedPattern level variable
            )
    splitStepResult
        StepResult { rewrittenPattern, remainder }
      =
        ( MultiOr.make [rewrittenPattern]
        , remainder
        )

{-| Takes a configuration and a set of rules and tries to apply them to the
configuration in order, using unification.

The first rule is applied on the entire configuration, while the subsequent
ones are applied on the part of configuration that was not transformed by the
previous ones.

See 'stepWithRemaindersForUnifier' for more details.
-}
stepWithRemainders
    ::  ( FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , OrdMetaOrObject variable
        , SortedVariable variable
        , Show (variable level)
        , ShowMetaOrObject variable
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from symbol IDs to defined functions
    -> ExpandedPattern level variable
    -- ^ Configuration being rewritten.
    -> [RewriteRule level variable]
    -- ^ Rewriting axiom
    -> Simplifier
        ( OrStepResult level variable
        , StepProof level variable
        )
stepWithRemainders
    tools substitutionSimplifier simplifier axiomIdToSimplifier patt rules
  = do
    resultOrError <- runExceptT
        $ stepWithRemaindersForUnifier
            tools
            (UnificationProcedure Unification.unificationProcedure)
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            (map (\ (RewriteRule rule) -> rule) rules)
            patt
    case resultOrError of
        Left _ -> error $
            "Not implemented error "
            ++ " while applying a \\rewrite axiom to the pattern."
            ++ " We decided to end the execution because we don't understand"
            ++ " this case well enough at the moment."
        Right result -> return result

unwrapStepErrorVariables
    :: Functor m
    => ExceptT (StepError level (StepperVariable variable)) m a
    -> ExceptT (StepError level                  variable ) m a
unwrapStepErrorVariables =
    withExceptT (mapStepErrorVariables unwrapStepperVariable)

unwrapPatternVariables
    ::  forall level variable m
    .   ( MetaOrObject level
        , Monad m
        , Ord (variable level)
        , Unparse (variable level)
        , FreshVariable variable
        )
    => StepPattern level (StepperVariable variable)
    -> m (StepPattern level variable)
unwrapPatternVariables = return . Pattern.mapVariables unwrapStepperVariable

unwrapPredicateVariables
    ::  forall level variable m
    .   ( MetaOrObject level
        , Monad m
        , Ord (variable level)
        , Unparse (variable level)
        , FreshVariable variable
        )
    => Predicate level (StepperVariable variable)
    -> m (Predicate level variable)
unwrapPredicateVariables = traverse unwrapPatternVariables

wrapUnificationOrSubstitutionError
    :: Functor m
    => ExceptT (UnificationOrSubstitutionError level variable) m a
    -> ExceptT (StepError                      level variable) m a
wrapUnificationOrSubstitutionError =
    withExceptT unificationOrSubstitutionToStepError

{- | Lift an action from the unifier into the stepper.
 -}
fromUnification
    :: Monad m
    => BranchT (ExceptT (UnificationOrSubstitutionError level variable) m) a
    -> BranchT (ExceptT (StepError level variable                     ) m) a
fromUnification = Monad.Morph.hoist wrapUnificationOrSubstitutionError

{- | Attempt to unify a rule with the initial configuration.

The rule variables are renamed to avoid collision with the
configuration. @unifyRule@ fails if unification fails. @unifyRule@ returns the
applied rule wrapped in the unification solution, but the rule is not yet
instantiated to the solution (see 'instantiateRule'). The initial conditions are
not applied to the rule (see 'applyRule').

 -}
unifyRule
    ::  ( Ord     (variable Object)
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
        (Predicated Object variable (RulePattern Object variable))
unifyRule
    metadataTools
    (UnificationProcedure unificationProcedure)
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers

    initial
    rule
  = do
    let configVariables = ExpandedPattern.freeVariables initial
        (_, renamed) = RulePattern.refreshRulePattern configVariables rule

        -- Wrap rule and configuration so that unification prefers to substitute
        -- axiom variables.
        rule' = RulePattern.mapVariables AxiomVariable renamed
        initial' = ExpandedPattern.mapVariables ConfigurationVariable initial
        RulePattern { left = ruleLeft } = rule'
        Predicated { term = initialTerm } = initial'
    unifier <- unifyPatterns ruleLeft initialTerm
    let unifier' =
            PredicateSubstitution.mapVariables unwrapStepperVariable unifier
    return (unifier' $> renamed)
  where
    unifyPatterns pat1 pat2 = do
        (unifiers, _) <-
            Monad.Morph.hoist unwrapStepErrorVariables
            $ fromUnification
            $ Monad.Trans.lift
            $ unificationProcedure
                metadataTools
                predicateSimplifier
                patternSimplifier
                axiomSimplifiers
                pat1
                pat2
        scatter unifiers

{- | Instantiate the rule by applying the unification solution.

The unification solution is normalized with the 'requires' clause from the
unified rule. @instantiateRule@ fails if normalization fails. @instantiateRule@
branches when the 'PredicateSubstitutionSimplifier' causes normalization to
branch.

 -}
instantiateRule
    ::  ( Ord     (variable Object)
        , Show    (variable Object)
        , Unparse (variable Object)
        , FreshVariable  variable
        , SortedVariable variable
        )
    => MetadataTools Object StepperAttributes
    -> PredicateSubstitutionSimplifier Object
    -> StepPatternSimplifier Object
    -> BuiltinAndAxiomSimplifierMap Object

    -> Predicated Object variable (RulePattern Object variable)
    -- ^ Rule and unification solution
    -> BranchT
        (ExceptT (StepError Object variable) Simplifier)
        (Predicated Object variable (RulePattern Object variable))
instantiateRule
    metadataTools
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers

    unified@Predicated { term = axiom@RulePattern { left, right, requires } }
  = do
    let unifier = unified { term = () }
        merged = PredicateSubstitution.fromPredicate requires *> unifier
    normalized <- normalize merged
    let Predicated { substitution } = normalized
        substitution' = Substitution.toMap substitution
        axiom' =
            axiom
                { left     = Pattern.substitute   substitution' left
                , right    = Pattern.substitute   substitution' right
                , requires = Predicate.substitute substitution' requires
                }
    return (normalized { term = axiom' })
  where
    normalize =
        fromUnification
        . Substitution.normalizeExcept
            metadataTools
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers

{- | Apply a rule to produce final configurations given some initial conditions.

The rule should be instantiated with 'instantiateRule'. The initial conditions
are merged with any conditions from the rule instantiation and
normalized. @applyRule@ fails if normalization fails. @applyRule@ branches when
the 'PredicateSubstitutionSimplifier' causes normalization to branch.

 -}
applyRule
    ::  ( Ord     (variable Object)
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
    -> Predicated Object variable (RulePattern Object variable)
    -- ^ Instantiated rule
    -> BranchT
        (ExceptT (StepError Object variable) Simplifier)
        (ExpandedPattern Object variable)
applyRule
    metadataTools
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers

    initial
    instantiated@Predicated { term = axiom }
  = do
    let merged = initial *> instantiated { term = () }
    normalized <- normalize merged
    return normalized { term = right axiom }
  where
    normalize =
        fromUnification
        . Substitution.normalizeExcept
            metadataTools
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers
