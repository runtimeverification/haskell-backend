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
    ( AxiomPattern (..)
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
    , stepWithAxiom
    , stepWithAxiomForUnifier
    ) where

import qualified Control.Arrow as Arrow
import           Control.Monad.Except
import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe, mapMaybe )
import           Data.Reflection
                 ( give )
import           Data.Semigroup
                 ( Semigroup (..) )
import           Data.Sequence
                 ( Seq )
import qualified Data.Sequence as Seq
import qualified Data.Set as Set

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( mapPatternVariables )
import           Kore.ASTUtils.SmartConstructors
                 ( mkBottom )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools, SymbolOrAliasSorts )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( Predicate, makeAndPredicate, makeNotPredicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Proof.Functional
                 ( FunctionalProof (..) )
import           Kore.Step.AxiomPatterns
import           Kore.Step.Error
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, PredicateSubstitution, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.ExpandedPattern as PredicateSubstitution
                 ( toPredicate )
import           Kore.Step.Pattern
import           Kore.Step.RecursiveAttributes
                 ( isFunctionPattern )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier (..),
                 SimplificationProof (..), Simplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutionsExcept )
import           Kore.Substitution.Class
                 ( Hashable (..), substitute )
import qualified Kore.Substitution.List as ListSubstitution
import           Kore.Unification.Data
                 ( UnificationProof (..) )
import           Kore.Unification.Error
                 ( UnificationOrSubstitutionError )
import           Kore.Unification.Procedure
                 ( unificationProcedure )
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Variables.Free
                 ( pureAllVariables )
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
    deriving (Show, Eq)

{-| 'VariableRenaming' represents a renaming of a variable.
-}
data VariableRenaming level variable = VariableRenaming
    { variableRenamingOriginal :: StepperVariable variable level
    , variableRenamingRenamed  :: StepperVariable variable level
    }
    deriving (Show, Eq)

{-| 'StepperVariable' wraps a variable in a variable-like type, distinguishing
variables by source.
-}
data StepperVariable variable level
    = AxiomVariable (Variable level)
    | ConfigurationVariable (variable level)
    deriving (Show, Ord, Eq)

instance
    SortedVariable variable
    => SortedVariable (StepperVariable variable)
  where
    sortedVariableSort (ConfigurationVariable variable) =
        sortedVariableSort variable
    sortedVariableSort (AxiomVariable variable) =
        sortedVariableSort variable

instance
    Hashable variable
    => Hashable (StepperVariable variable)
  where
    -- TODO(virgil): For performance reasons, this should generate different
    -- hashes for axiom and configuration variables.
    getVariableHash (ConfigurationVariable variable) =
        getVariableHash variable
    getVariableHash (AxiomVariable variable) =
        getVariableHash variable

instance
    FreshVariable variable
    => FreshVariable (StepperVariable variable)
  where
    freshVariableFromVariable var n =
        ConfigurationVariable (freshVariableFromVariable var n)
    freshVariableWith (AxiomVariable a) n =
        ConfigurationVariable $ freshVariableFromVariable a n
    freshVariableWith (ConfigurationVariable a) n =
        ConfigurationVariable $ freshVariableWith a n

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

{-| 'stepProofSumName' extracts the constructor name for a 'StepProof' -}
stepProofSumName :: StepProofAtom variable level -> String
stepProofSumName (StepProofUnification _)       = "StepProofUnification"
stepProofSumName (StepProofVariableRenamings _) = "StepProofVariableRenamings"
stepProofSumName (StepProofSimplification _)    = "StepProofSimplification"

-- | Wraps functions such as 'unificationProcedure' and
-- 'Kore.Step.Function.Matcher.matchAsUnification' to be used in
-- 'stepWithAxiomForUnifier'.
newtype UnificationProcedure level =
    UnificationProcedure
        ( forall variable m
        .   ( SortedVariable variable
            , Ord (variable level)
            , Show (variable level)
            , OrdMetaOrObject variable
            , ShowMetaOrObject variable
            , MetaOrObject level
            , Hashable variable
            , FreshVariable variable
            , MonadCounter m
            )
        => MetadataTools level StepperAttributes
        -> PredicateSubstitutionSimplifier level m
        -> StepPattern level variable
        -> StepPattern level variable
        -> ExceptT
            (UnificationOrSubstitutionError level variable)
            m
            ( PredicateSubstitution level variable
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
stepWithAxiomForUnifier
    :: forall level variable .
        ( FreshVariable variable
        , Hashable variable
        , MetaOrObject level
        , Ord (variable level)
        , OrdMetaOrObject variable
        , SortedVariable variable
        , Show (variable level)
        , ShowMetaOrObject variable
        )
    => MetadataTools level StepperAttributes
    -> UnificationProcedure level
    -> PredicateSubstitutionSimplifier level Simplifier
    -> ExpandedPattern level variable
    -- ^ Configuration being rewritten.
    -> AxiomPattern level
    -- ^ Rewriting axiom
    -> ExceptT
        (StepError level variable)
        Simplifier
        ( StepResult level variable
        , StepProof level variable
        )
stepWithAxiomForUnifier
    tools
    (UnificationProcedure unificationProcedure')
    substitutionSimplifier
    expandedPattern@Predicated
        { term = initialTerm
        , substitution = initialSubstitution
        }
    axiom@AxiomPattern
        { axiomPatternLeft = axiomLeftRaw
        , axiomPatternRight = axiomRightRaw
        , axiomPatternRequires = axiomRequiresRaw
        }
  = do
    -- Distinguish configuration (pattern) and axiom variables by lifting them
    -- into 'StepperVariable'.
    let
        Predicated
            { term = startPattern
            , predicate = startCondition
            , substitution = startSubstitution
            } =
                ExpandedPattern.mapVariables
                    ConfigurationVariable expandedPattern
        wrapAxiomVariables = mapPatternVariables AxiomVariable
        axiomLeft = wrapAxiomVariables axiomLeftRaw
        axiomRight = wrapAxiomVariables axiomRightRaw
        axiomRequires = Predicate.mapVariables AxiomVariable axiomRequiresRaw

    let
        -- Keep a set of all variables for remapping errors (below).
        existingVars =
            Set.map
                ConfigurationVariable
                (ExpandedPattern.allVariables expandedPattern)
            <> Set.map AxiomVariable (pureAllVariables axiomLeftRaw)
            <> Set.map AxiomVariable (pureAllVariables axiomRightRaw)
            <> Set.map AxiomVariable (Predicate.allVariables axiomRequiresRaw)

        -- Remap unification and substitution errors into 'StepError'.
        normalizeUnificationOrSubstitutionError
            ::  ( FreshVariable variable
                , MetaOrObject level
                , Ord (variable level)
                , Show (variable level)
                )
            => Set.Set (StepperVariable variable level)
            -> ExceptT
                (UnificationOrSubstitutionError
                    level
                    (StepperVariable variable)
                )
                Simplifier
                a
            -> ExceptT (StepError level variable) Simplifier a
        normalizeUnificationOrSubstitutionError existingVariables action =
            stepperVariableToVariableForError
                existingVariables
                $ withExceptT unificationOrSubstitutionToStepError action

    -- Unify the left-hand side of the rewriting axiom with the initial
    -- configuration, producing a substitution (instantiating the axiom to the
    -- configuration) subject to a predicate.
    ( Predicated
            { predicate = rawPredicate
            , substitution = rawSubstitution
            }
        , rawSubstitutionProof
        ) <- normalizeUnificationOrSubstitutionError
                existingVars
                (unificationProcedure'
                    tools
                    substitutionSimplifier
                    axiomLeft
                    startPattern
                )

    -- Combine the all the predicates and substitutions generated above and
    -- simplify the result.
    ( Predicated
            { predicate = normalizedCondition
            , substitution = normalizedSubstitution
            }
        , _proof
        ) <- stepperVariableToVariableForError existingVars
            $ withExceptT unificationOrSubstitutionToStepError
            $ mergePredicatesAndSubstitutionsExcept
                tools
                substitutionSimplifier
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
        ) <- stepperVariableToVariableForError existingVars
            $ withExceptT unificationOrSubstitutionToStepError
            $ mergePredicatesAndSubstitutionsExcept
                tools
                substitutionSimplifier
                [ axiomRequires  -- from axiom
                , rawPredicate   -- produced during unification
                ]
                [rawSubstitution]

    let
        negatedRemainder =
            give sortTools $ makeNotPredicate $
                PredicateSubstitution.toPredicate
                    Predicated
                        { term = ()
                        , predicate = normalizedRemainderPredicateRaw
                        , substitution =
                            -- Note that this filtering is reasonable only
                            -- because below we check that there are no axiom
                            -- variables left in the predicate.
                            Substitution.modify
                                (filter hasConfigurationVariable)
                                normalizedRemainderSubstitution
                        }
        -- the remainder predicate is the start predicate from which we
        -- remove what was handled by the current axiom, i.e. we `and` it with
        -- the negated unification results and the axiom condition.
        normalizedRemainderPredicate =
            give sortTools $ makeAndPredicate
                startCondition  -- from initial configuration
                negatedRemainder
        hasConfigurationVariable :: (StepperVariable variable level, a) -> Bool
        hasConfigurationVariable (AxiomVariable _, _) = False
        hasConfigurationVariable (ConfigurationVariable _, _) = True

    let
        rawNormalizedSubstitution = Substitution.unwrap normalizedSubstitution
        unifiedSubstitution =
            ListSubstitution.fromList
                (makeUnifiedSubstitution rawNormalizedSubstitution)
    -- Apply substitution to resulting configuration and conditions.
    rawResult <- substitute axiomRight unifiedSubstitution

    let
        variablesInLeftAxiom =
            pureAllVariables axiomLeftRaw
            <> extractAxiomVariables
                (Predicate.allVariables normalizedCondition)
            <> extractAxiomVariables
                (Predicate.allVariables normalizedRemainderPredicate)
        toVariable :: StepperVariable variable level -> Maybe (Variable level)
        toVariable (AxiomVariable v) = Just v
        toVariable (ConfigurationVariable _) = Nothing
        extractAxiomVariables
            :: Set.Set (StepperVariable variable level)
            -> Set.Set (Variable level)
        extractAxiomVariables =
            Set.fromList . mapMaybe toVariable . Set.toList
        substitutions =
            Set.fromList . mapMaybe (toVariable . fst)
            $ rawNormalizedSubstitution

    -- Unwrap internal 'StepperVariable's and collect the variable mappings
    -- for the proof.
    (variableMapping, result) <-
        lift
        $ patternStepVariablesToCommon
            existingVars Map.empty rawResult
    (variableMapping1, condition) <-
        lift
        $ predicateStepVariablesToCommon
            existingVars variableMapping normalizedCondition
    (variableMapping2, remainderPredicate) <-
        lift
        $ predicateStepVariablesToCommon
            existingVars variableMapping1 normalizedRemainderPredicate
    (variableMapping3, substitutionProof) <-
        lift
        $ unificationProofStepVariablesToCommon
            existingVars variableMapping2 rawSubstitutionProof

    if Predicate.isFalse condition
       || variablesInLeftAxiom `Set.isSubsetOf` substitutions
        then return ()
        else
            (error . unlines)
            [ "While applying axiom:", show axiom
            , "to configuration:", show expandedPattern
            , "Unexpected non-false predicate:", show condition
            , "when substitutions:", show substitutions
            , "do not cover all variables in left axiom:", show variablesInLeftAxiom
            ]

    let
        orElse :: a -> a -> a
        p1 `orElse` p2 = if Predicate.isFalse condition then p2 else p1
    return
        ( StepResult
            { rewrittenPattern = Predicated
                { term = result `orElse` mkBottom
                , predicate = condition
                -- TODO(virgil): Can there be unused variables? Should we
                -- remove them?
                , substitution =
                    Substitution.mapVariables
                        configurationVariableToCommon
                        (removeAxiomVariables normalizedSubstitution)
                    `orElse` mempty
                }
            , remainder =
                if not (isFunctionPattern tools initialTerm)
                then error
                    (  "Cannot handle non-function patterns, \
                       \see design-decisions/\
                       \2018-10-24-And-Not-Exists-Simplification.md \
                       \for hints on how to fix:"
                    ++ show initialTerm
                    )
                else if not (isFunctionPattern tools axiomLeftRaw)
                then error
                    (  "Cannot handle non-function patterns, \
                       \see design-decisions/\
                       \2018-10-24-And-Not-Exists-Simplification.md \
                       \for hints on how to fix:"
                    ++ show axiomLeftRaw
                    )
                else Predicated
                    { term = initialTerm
                    , predicate = remainderPredicate
                    , substitution = initialSubstitution
                    }
            }
        , (<>)
            ((stepProof . StepProofVariableRenamings)
                (variablePairToRenaming <$> Map.toList variableMapping3)
            )
            ((stepProof . StepProofUnification) substitutionProof)
        )
  where
    -- | Unwrap 'StepperVariable's so that errors are not expressed in terms of
    -- internally-defined variables.
    stepperVariableToVariableForError
        :: forall a
        .   ( FreshVariable variable
            , MetaOrObject level
            , Ord (variable level)
            , Show (variable level)
            )
        => Set.Set (StepperVariable variable level)
        -> ExceptT (StepError level (StepperVariable variable)) Simplifier a
        -> ExceptT (StepError level variable) Simplifier a
    stepperVariableToVariableForError existingVars = mapExceptT mapper
      where
        mapper
            :: Simplifier
                (Either (StepError level (StepperVariable variable)) a)
            -> Simplifier (Either (StepError level variable) a)
        mapper action = do
            result <- action
            case result of
                Right value -> return (Right value)
                Left err -> do
                    let axiomVars = stepErrorVariables err
                    mapping <-
                        addAxiomVariablesAsConfig
                            existingVars Map.empty (Set.toList axiomVars)
                    let errorWithoutAxiomVars =
                            mapStepErrorVariables
                                (\var -> fromMaybe var (Map.lookup var mapping))
                                err
                    return $ Left $ mapStepErrorVariables
                        configurationVariableToCommon errorWithoutAxiomVars

    variablePairToRenaming
        :: (StepperVariable variable level, StepperVariable variable level)
        -> VariableRenaming level variable
    variablePairToRenaming (original, renamed) = VariableRenaming
        { variableRenamingOriginal = original
        , variableRenamingRenamed  = renamed
        }
    sortTools :: SymbolOrAliasSorts level
    sortTools = MetadataTools.symbolOrAliasSorts tools

stepWithAxiom
    ::  ( FreshVariable variable
        , Hashable variable
        , MetaOrObject level
        , Ord (variable level)
        , OrdMetaOrObject variable
        , SortedVariable variable
        , Show (variable level)
        , ShowMetaOrObject variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level Simplifier
    -> ExpandedPattern level variable
    -- ^ Configuration being rewritten.
    -> AxiomPattern level
    -- ^ Rewriting axiom
    -> ExceptT
        (StepError level variable)
        Simplifier
        ( StepResult level variable
        , StepProof level variable
        )
stepWithAxiom tools substitutionSimplifier =
    stepWithAxiomForUnifier
        tools
        (UnificationProcedure unificationProcedure)
        substitutionSimplifier

unificationProofStepVariablesToCommon
    ::  ( FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        )
    => Set.Set (StepperVariable variable level)
    -> Map.Map (StepperVariable variable level) (StepperVariable variable level)
    -> UnificationProof level (StepperVariable variable)
    -> Simplifier
        ( Map.Map
            (StepperVariable variable level)
            (StepperVariable variable level)
        , UnificationProof level variable
        )
unificationProofStepVariablesToCommon _ mapping EmptyUnificationProof =
    return (mapping, EmptyUnificationProof)
unificationProofStepVariablesToCommon
    existingVars
    mapping
    (CombinedUnificationProof items)
  = do
    (newMapping, mappedItems) <-
        listStepVariablesToCommon
            unificationProofStepVariablesToCommon existingVars mapping items
    return
        ( newMapping
        , CombinedUnificationProof mappedItems
        )
unificationProofStepVariablesToCommon
    existingVars
    mapping
    (ConjunctionIdempotency patt)
  = do
    (newMapping, mappedPattern) <-
        patternStepVariablesToCommon existingVars mapping patt
    return (newMapping, ConjunctionIdempotency mappedPattern)
unificationProofStepVariablesToCommon
    existingVars
    mapping
    (Proposition_5_24_3 functionalProof variable patt)
  = do
    (newMapping1, mappedVariable) <-
        variableStepVariablesToCommon existingVars mapping variable
    (newMapping2, mappedFunctionalProof) <-
        listStepVariablesToCommon
            functionalProofStepVariablesToCommon
            existingVars
            newMapping1
            functionalProof
    (newMapping3, mappedPattern) <-
        patternStepVariablesToCommon
            existingVars
            newMapping2
            patt
    return
        ( newMapping3
        , Proposition_5_24_3
            mappedFunctionalProof
            mappedVariable
            mappedPattern
        )
unificationProofStepVariablesToCommon
    existingVars
    mapping
    (AndDistributionAndConstraintLifting symbolOrAlias unificationProof)
  = do
    (newMapping, mappedItems) <-
        listStepVariablesToCommon
            unificationProofStepVariablesToCommon
            existingVars
            mapping
            unificationProof
    return
        ( newMapping
        , AndDistributionAndConstraintLifting
            symbolOrAlias
            mappedItems
        )
unificationProofStepVariablesToCommon
    existingVars
    mapping
    (SubstitutionMerge variable patt1 patt2)
  = do
    (newMapping1, mappedVariable) <-
        variableStepVariablesToCommon existingVars mapping variable
    (newMapping2, mappedPattern1) <-
        patternStepVariablesToCommon existingVars newMapping1 patt1
    (newMapping3, mappedPattern2) <-
        patternStepVariablesToCommon existingVars newMapping2 patt2
    return
        ( newMapping3
        , SubstitutionMerge
            mappedVariable
            mappedPattern1
            mappedPattern2
        )

listStepVariablesToCommon
    :: MetaOrObject level
    =>  (Set.Set (StepperVariable variable level)
            -> Map.Map
                (StepperVariable variable level)
                (StepperVariable variable level)
            -> listElement (StepperVariable variable)
            -> Simplifier
                ( Map.Map
                    (StepperVariable variable level)
                    (StepperVariable variable level)
                , listElement variable
                )
        )
    -> Set.Set (StepperVariable variable level)
    -> Map.Map (StepperVariable variable level) (StepperVariable variable level)
    -> [listElement (StepperVariable variable)]
    -> Simplifier
        ( Map.Map
            (StepperVariable variable level)
            (StepperVariable variable level)
        , [listElement variable]
        )
listStepVariablesToCommon _ _ mapping [] =
    return (mapping, [])
listStepVariablesToCommon elementMapper existingVars mapping (proof : proofs)
  = do
    (newMapping1, mappedProof) <- elementMapper existingVars mapping proof
    (newMapping2, mappedProofs) <-
        listStepVariablesToCommon elementMapper existingVars newMapping1 proofs
    return (newMapping2, mappedProof : mappedProofs)

functionalProofStepVariablesToCommon
    ::  ( FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        )
    => Set.Set (StepperVariable variable level)
    -> Map.Map (StepperVariable variable level) (StepperVariable variable level)
    -> FunctionalProof level (StepperVariable variable)
    -> Simplifier
        ( Map.Map
            (StepperVariable variable level)
            (StepperVariable variable level)
        , FunctionalProof level variable
        )
functionalProofStepVariablesToCommon
    existingVars mapping (FunctionalVariable variable)
  = do
    (newMapping, mappedVariable) <-
        variableStepVariablesToCommon existingVars mapping variable
    return (newMapping, FunctionalVariable mappedVariable)
functionalProofStepVariablesToCommon _ mapping (FunctionalHead f) =
    return (mapping, FunctionalHead f)
functionalProofStepVariablesToCommon _ mapping (FunctionalStringLiteral sl) =
    return (mapping, FunctionalStringLiteral sl)
functionalProofStepVariablesToCommon _ mapping (FunctionalCharLiteral cl) =
    return (mapping, FunctionalCharLiteral cl)
functionalProofStepVariablesToCommon _ mapping (FunctionalDomainValue dv) =
    return (mapping, FunctionalDomainValue dv)

variableStepVariablesToCommon
    ::  ( FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        )
    => Set.Set (StepperVariable variable level)
    -> Map.Map (StepperVariable variable level) (StepperVariable variable level)
    -> StepperVariable variable level
    -> Simplifier
        ( Map.Map
            (StepperVariable variable level)
            (StepperVariable variable level)
        , variable level
        )
variableStepVariablesToCommon existingVars mapping variable =
    case variable of
        ConfigurationVariable v -> return (mapping, v)
        AxiomVariable _ ->
            case Map.lookup variable mapping of
                Just var ->
                    case var of
                        AxiomVariable _         ->
                            error "Unexpected axiom variable"
                        ConfigurationVariable v -> return (mapping, v)
                Nothing -> do
                    newVar <-
                        freshVariableSuchThat
                            variable
                            ( not . (`Set.member` existingVars) )
                    unwrappedNewVar <-
                        case newVar of
                            (ConfigurationVariable v) -> return v
                            _ -> error
                                (  "Unexpected new variable type: "
                                ++ show newVar
                                )
                    return
                        ( Map.insert variable newVar mapping
                        , unwrappedNewVar
                        )

predicateStepVariablesToCommon
    ::  ( FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        )
    => Set.Set (StepperVariable variable level)
    -> Map.Map (StepperVariable variable level) (StepperVariable variable level)
    -> Predicate level (StepperVariable variable)
    -> Simplifier
        ( Map.Map
            (StepperVariable variable level)
            (StepperVariable variable level)
        , Predicate level variable
        )
predicateStepVariablesToCommon existingVars mapped predicate' = do
    let axiomVars = Predicate.allVariables predicate'
    mapping <-
        addAxiomVariablesAsConfig existingVars mapped (Set.toList axiomVars)
    return
        ( mapping
        , fmap
            (configurationVariablesToCommon . replacePatternVariables mapping)
            predicate'
        )
  where
    configurationVariablesToCommon =
        mapPatternVariables configurationVariableToCommon

patternStepVariablesToCommon
    ::  ( FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        )
    => Set.Set (StepperVariable variable level)
    -> Map.Map (StepperVariable variable level) (StepperVariable variable level)
    -> StepPattern level (StepperVariable variable)
    -> Simplifier
        ( Map.Map
            (StepperVariable variable level)
            (StepperVariable variable level)
        , StepPattern level variable
        )
patternStepVariablesToCommon existingVars mapped patt = do
    let axiomVars = pureAllVariables patt
    mapping <-
        addAxiomVariablesAsConfig existingVars mapped (Set.toList axiomVars)
    return
        ( mapping
        , configurationVariablesToCommon (replacePatternVariables mapping patt)
        )
  where
    configurationVariablesToCommon =
        mapPatternVariables configurationVariableToCommon

configurationVariableToCommon
    :: StepperVariable variable level -> variable level
configurationVariableToCommon (AxiomVariable a) =
    error ("Unexpected AxiomVariable: '" ++ show a ++ "'.")
configurationVariableToCommon (ConfigurationVariable v) = v

replacePatternVariables
    ::  ( MetaOrObject level
        , Ord (variable level)
        )
    => Map.Map (StepperVariable variable level) (StepperVariable variable level)
    -> StepPattern level (StepperVariable variable)
    -> StepPattern level (StepperVariable variable)
replacePatternVariables mapping =
    mapPatternVariables
        (\var -> fromMaybe var (Map.lookup var mapping))

addAxiomVariablesAsConfig
    ::  ( FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        )
    => Set.Set (StepperVariable variable level)
    -> Map.Map (StepperVariable variable level) (StepperVariable variable level)
    -> [StepperVariable variable level]
    -> Simplifier
        (Map.Map
            (StepperVariable variable level)
            (StepperVariable variable level)
        )
addAxiomVariablesAsConfig _ mapping [] = return mapping
addAxiomVariablesAsConfig
    existingVars mapping (ConfigurationVariable _ : vars)
  =
    addAxiomVariablesAsConfig existingVars mapping vars
addAxiomVariablesAsConfig
    existingVars mapping (var@(AxiomVariable _) : vars)
  =
    case Map.lookup var mapping of
        Just _ -> addAxiomVariablesAsConfig existingVars mapping vars
        Nothing -> do
            newVar <-
                freshVariableSuchThat
                    var
                    ( not . (`Set.member` existingVars) )
            case newVar of
                (ConfigurationVariable _) -> return ()
                _ -> error
                    ("Unexpected new variable type: " ++ show newVar)
            addAxiomVariablesAsConfig
                existingVars
                (Map.insert var newVar mapping)
                vars

removeAxiomVariables
    :: MetaOrObject level
    => Substitution level (StepperVariable variable)
    -> Substitution level (StepperVariable variable)
removeAxiomVariables =
    Substitution.wrap
    . filter
        (\ (variable, _) -> case variable of
            AxiomVariable _         -> False
            ConfigurationVariable _ -> True
        )
    . Substitution.unwrap

makeUnifiedSubstitution
    :: MetaOrObject level
    => [( StepperVariable variable level
        , StepPattern level (StepperVariable variable)
        )]
    -> [(Unified (StepperVariable variable)
        , StepPattern level (StepperVariable variable)
        )]
makeUnifiedSubstitution =
    map (Arrow.first asUnified)
