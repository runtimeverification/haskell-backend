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
    , StepperVariable (..)
    , StepProof (..)
    , StepProofAtom (..)
    , VariableRenaming (..)
    , simplificationProof
    , stepProof
    , stepProofSumName
    , stepWithAxiom
    ) where

import qualified Control.Arrow as Arrow
import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe )
import           Data.Reflection
                 ( Given, give )
import           Data.Semigroup
                 ( Semigroup (..) )
import           Data.Sequence
                 ( Seq )
import qualified Data.Sequence as Seq
import qualified Data.Set as Set

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( CommonPurePattern, PureMLPattern, mapPatternVariables )
import           Kore.ASTUtils.SmartConstructors
                 ( mkBottom )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SortTools )
import           Kore.Predicate.Predicate
                 ( Predicate, PredicateProof (..), makeFalsePredicate,
                 makeMultipleAndPredicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.AxiomPatterns
import           Kore.Step.Error
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern),
                 PredicateSubstitution (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.PatternAttributes
                 ( FunctionalProof (..) )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Substitution
                 ( mergeAndNormalizeSubstitutions )
import           Kore.Substitution.Class
                 ( Hashable (..), PatternSubstitutionClass (..) )
import qualified Kore.Substitution.List as ListSubstitution
import           Kore.Unification.Error
                 ( UnificationError )
import           Kore.Unification.Unifier
                 ( UnificationProof (..), UnificationSubstitution,
                 mapSubstitutionVariables, unificationProcedure )
import           Kore.Variables.Free
                 ( pureAllVariables )
import           Kore.Variables.Fresh

{-| 'StepperConfiguration' represents the configuration to which a rewriting
axiom is applied.

A configuration consists of a pattern and a condition predicate, and would be
represented as pattern /\ condition-predicate in Kore.
--}
data StepperConfiguration level = StepperConfiguration
    { stepperConfigurationPattern       :: !(CommonPurePattern level)
    -- ^ The pattern being rewritten.

    , stepperConfigurationCondition     :: !(CommonPurePattern level)
    -- ^ The condition predicate.
    -- TODO(virgil): Make this an EvaluatedCondition.
    }
    deriving (Show, Eq)

{- | 'StepProof' is the proof for an execution step or steps.
 -}
newtype StepProof level = StepProof { getStepProof :: Seq (StepProofAtom level) }
  deriving (Eq, Show)

instance Semigroup (StepProof level) where
    (<>) (StepProof a) (StepProof b) = StepProof (a <> b)

instance Monoid (StepProof level) where
    mempty = StepProof mempty
    mappend = (<>)

stepProof :: StepProofAtom level -> StepProof level
stepProof atom = StepProof (Seq.singleton atom)

simplificationProof :: SimplificationProof level -> StepProof level
simplificationProof = stepProof . StepProofSimplification

{- | The smallest unit of a 'StepProof'.

  @StepProofAtom@ encapsulates the separate proofs resulting from unification,
  variable renaming, and simplification.

 -}
data StepProofAtom level
    = StepProofUnification !(UnificationProof level Variable)
    -- ^ Proof for a unification that happened during the step.
    | StepProofVariableRenamings [VariableRenaming level]
    -- ^ Proof for the remanings that happened during ther proof.
    | StepProofSimplification !(SimplificationProof level)
    -- ^ Proof for the simplification part of a step.
    deriving (Show, Eq)

{-| 'VariableRenaming' represents a renaming of a variable.
-}
data VariableRenaming level = VariableRenaming
    { variableRenamingOriginal :: StepperVariable level
    , variableRenamingRenamed  :: StepperVariable level
    }
    deriving (Show, Eq)

{-| 'StepperVariable' wraps a variable in a variable-like type, distinguishing
variables by source.
-}
data StepperVariable level
    = AxiomVariable (Variable level)
    | ConfigurationVariable (Variable level)
    deriving (Show, Ord, Eq)

instance SortedVariable StepperVariable where
    sortedVariableSort = sortedVariableSort . getStepperVariableVariable

instance Hashable StepperVariable where
    -- TODO(virgil): For performance reasons, this should generate different
    -- hashes for axiom and configuration variables.
    getVariableHash = getVariableHash . getStepperVariableVariable

instance FreshVariable StepperVariable where
    freshVariableWith (AxiomVariable a) =
        AxiomVariable <$> freshVariableWith a
    freshVariableWith (ConfigurationVariable a) =
        ConfigurationVariable <$> freshVariableWith a

{-| 'getStepperVariableVariable' extracts the initial variable from a stepper
one.
-}
getStepperVariableVariable :: StepperVariable level -> Variable level
getStepperVariableVariable (AxiomVariable a)         = a
getStepperVariableVariable (ConfigurationVariable a) = a

{-| 'stepProofSumName' extracts the constructor name for a 'StepProof' -}
stepProofSumName :: StepProofAtom level -> String
stepProofSumName (StepProofUnification _)       = "StepProofUnification"
stepProofSumName (StepProofVariableRenamings _) = "StepProofVariableRenamings"
stepProofSumName (StepProofSimplification _)    = "StepProofSimplification"

{- |
    Use the given axiom to execute a single rewriting step.

    Does not properly handle various cases, among them:
    - sigma(x, y) => y    vs    a

    Returns 'Left' only if there is an error. It is not an error if the axiom
    does not apply to the given configuration.
-}
stepWithAxiom
    ::  ( MetaOrObject level )
    => MetadataTools level StepperAttributes
    -> ExpandedPattern.CommonExpandedPattern level
    -- ^ Configuration being rewritten.
    -> AxiomPattern level
    -- ^ Rewriting axiom
    -> Either
        (Counter (StepError level Variable))
        (Counter
            (ExpandedPattern.CommonExpandedPattern level, StepProof level)
        )
stepWithAxiom
    tools
    expandedPattern
    AxiomPattern
        { axiomPatternLeft = axiomLeftRaw
        , axiomPatternRight = axiomRightRaw
        , axiomPatternRequires = axiomRequiresRaw
        }
  = do
    -- Distinguish configuration (pattern) and axiom variables by lifting them
    -- into 'StepperVariable'.
    let
        wrappedExpandedPattern =
            ExpandedPattern.mapVariables ConfigurationVariable expandedPattern
        (startPattern, startCondition, startSubstitution) =
            case wrappedExpandedPattern of
                ExpandedPattern { term, predicate, substitution } ->
                    (term, predicate, substitution)
        wrapAxiomVariables = mapPatternVariables AxiomVariable
        axiomLeft = wrapAxiomVariables axiomLeftRaw
        axiomRight = wrapAxiomVariables axiomRightRaw
        axiomRequires = Predicate.mapVariables AxiomVariable axiomRequiresRaw

    let
        -- Keep a set of all variables for remapping errors (below).
        existingVars =
            ExpandedPattern.allVariables expandedPattern
            <> pureAllVariables axiomLeftRaw
            <> pureAllVariables axiomRightRaw
            <> Predicate.allVariables axiomRequiresRaw

        -- Remap unification and substitution errors into 'StepError'.
        normalizeUnificationError
            :: MetaOrObject level
            => a
            -- ^element of the target symbolizing a 'Bottom'-like result
            -> Set.Set (Variable level)
            -> Either (UnificationError level) a
            -> Either (Counter (StepError level Variable)) a
        normalizeUnificationError bottom existingVariables action =
            stepperVariableToVariableForError
                existingVariables (unificationToStepError bottom action)

    -- Unify the left-hand side of the rewriting axiom with the initial
    -- configuration, producing a substitution (instantiating the axiom to the
    -- configuration) subject to a predicate.
    (     unificationSubstitution
        , unificationCondition
        , rawSubstitutionProof
        ) <-
            normalizeUnificationError
                ([], makeFalsePredicate, EmptyUnificationProof)
                existingVars
                (unificationProcedure
                    tools
                    axiomLeft
                    startPattern
                )

    -- Combine the substitution produced by unification with the initial
    -- substitution carried by the configuration. Merging substitutions may
    -- produce another predicate during symbolic execution.
    normalizedSubstitutionWithCounter <-
        stepperVariableToVariableForError
            existingVars
            $ unificationOrSubstitutionToStepError
            $ mergeAndNormalizeSubstitutions tools unificationSubstitution startSubstitution

    return $ do
        ( PredicateSubstitution
              { predicate = normalizedCondition
              , substitution = normalizedSubstitution
              }
          , _  -- TODO: Use this proof
          ) <- normalizedSubstitutionWithCounter

        let
            unifiedSubstitution =
                ListSubstitution.fromList
                    (makeUnifiedSubstitution normalizedSubstitution)
        -- Merge all conditions collected so far
            (mergedConditionWithCounter, _) = -- TODO: Use this proof
                give (sortTools tools)
                $ mergeConditionsWithAnd
                    [ startCondition  -- from initial configuration
                    , axiomRequires  -- from axiom
                    , unificationCondition  -- produced during unification
                    , normalizedCondition -- from normalizing the substitution
                    ]

        -- Apply substitution to resulting configuration and conditions.
        rawResult <- substitute axiomRight unifiedSubstitution

        normalizedMergedCondition <- mergedConditionWithCounter
        rawCondition <-
            traverse
                (`substitute` unifiedSubstitution)
                normalizedMergedCondition

        -- Unwrap internal 'StepperVariable's and collect the variable mappings
        -- for the proof.
        (variableMapping, result) <-
            patternStepVariablesToCommon existingVars Map.empty rawResult
        (variableMapping1, condition) <-
            predicateStepVariablesToCommon
                existingVars variableMapping rawCondition
        (variableMapping2, substitutionProof) <-
            unificationProofStepVariablesToCommon
                existingVars variableMapping1 rawSubstitutionProof
        let
            orElse :: a -> a -> a
            p1 `orElse` p2 = if Predicate.isFalse condition then p2 else p1
        return
            ( ExpandedPattern
                { term = result `orElse` mkBottom
                , predicate = condition
                -- TODO(virgil): Can there be unused variables? Should we
                -- remove them?
                , substitution =
                    mapSubstitutionVariables
                        configurationVariableToCommon
                        (removeAxiomVariables normalizedSubstitution)
                    `orElse` []
                }
            , (<>)
              ((stepProof . StepProofVariableRenamings)
               (variablePairToRenaming <$> Map.toList variableMapping2)
              )
              ((stepProof . StepProofUnification) substitutionProof)
            )
  where
    -- | Unwrap 'StepperVariable's so that errors are not expressed in terms of
    -- internally-defined variables.
    stepperVariableToVariableForError
        :: MetaOrObject level
        => Set.Set (Variable level)
        -> Either (StepError level StepperVariable) a
        -> Either (Counter (StepError level Variable)) a
    stepperVariableToVariableForError existingVars action =
        case action of
            Left err -> Left $ do
                let axiomVars = stepErrorVariables err
                mapping <-
                    addAxiomVariablesAsConfig
                        existingVars Map.empty (Set.toList axiomVars)
                let errorWithoutAxiomVars =
                        mapStepErrorVariables
                            (\var -> fromMaybe var (Map.lookup var mapping))
                            err
                return $ mapStepErrorVariables
                    configurationVariableToCommon errorWithoutAxiomVars
            Right result -> Right result

    variablePairToRenaming
        :: (StepperVariable level, StepperVariable level)
        -> VariableRenaming level
    variablePairToRenaming (original, renamed) = VariableRenaming
        { variableRenamingOriginal = original
        , variableRenamingRenamed  = renamed
        }

mergeConditionsWithAnd
    ::  ( MetaOrObject level
        , Given (SortTools level)
        , SortedVariable var
        , Eq (var level)
        , Show (var level))
    => [Predicate level var]
    -> (Counter (Predicate level var), PredicateProof level)
mergeConditionsWithAnd conditions =
    let
        (predicate, proof) = makeMultipleAndPredicate conditions
    in
        (return predicate, proof)

unificationProofStepVariablesToCommon
    :: MetaOrObject level
    => Set.Set (Variable level)
    -> Map.Map (StepperVariable level) (StepperVariable level)
    -> UnificationProof level StepperVariable
    -> Counter
        ( Map.Map (StepperVariable level) (StepperVariable level)
        , UnificationProof level Variable
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
    =>  (Set.Set (Variable level)
            -> Map.Map (StepperVariable level) (StepperVariable level)
            -> listElement StepperVariable
            -> Counter
                ( Map.Map (StepperVariable level) (StepperVariable level)
                , listElement Variable
                )
        )
    -> Set.Set (Variable level)
    -> Map.Map (StepperVariable level) (StepperVariable level)
    -> [listElement StepperVariable]
    -> Counter
        ( Map.Map (StepperVariable level) (StepperVariable level)
        , [listElement Variable]
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
    :: MetaOrObject level
    => Set.Set (Variable level)
    -> Map.Map (StepperVariable level) (StepperVariable level)
    -> FunctionalProof level StepperVariable
    -> Counter
        ( Map.Map (StepperVariable level) (StepperVariable level)
        , FunctionalProof level Variable
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
    :: MetaOrObject level
    => Set.Set (Variable level)
    -> Map.Map (StepperVariable level) (StepperVariable level)
    -> StepperVariable level
    -> Counter
        ( Map.Map (StepperVariable level) (StepperVariable level)
        , Variable level
        )
variableStepVariablesToCommon existingVars mapping variable =
    case variable of
        ConfigurationVariable v -> return (mapping, v)
        AxiomVariable av ->
            case Map.lookup variable mapping of
                Just var ->
                    case var of
                        AxiomVariable _         ->
                            error "Unexpected axiom variable"
                        ConfigurationVariable v -> return (mapping, v)
                Nothing -> do
                    newVar <-
                        freshVariableSuchThat
                            av
                            ( not . (`Set.member` existingVars) )
                    return
                        ( Map.insert
                            variable (ConfigurationVariable newVar) mapping
                        , newVar
                        )

predicateStepVariablesToCommon
    :: MetaOrObject level
    => Set.Set (Variable level)
    -> Map.Map (StepperVariable level) (StepperVariable level)
    -> Predicate level StepperVariable
    -> Counter
        ( Map.Map (StepperVariable level) (StepperVariable level)
        , Predicate level Variable
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
    :: MetaOrObject level
    => Set.Set (Variable level)
    -> Map.Map (StepperVariable level) (StepperVariable level)
    -> PureMLPattern level StepperVariable
    -> Counter
        ( Map.Map (StepperVariable level) (StepperVariable level)
        , PureMLPattern level Variable
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

configurationVariableToCommon :: StepperVariable level -> Variable level
configurationVariableToCommon (AxiomVariable a) =
    error ("Unexpected AxiomVariable: '" ++ show a ++ "'.")
configurationVariableToCommon (ConfigurationVariable v) = v

replacePatternVariables
    :: MetaOrObject level
    => Map.Map (StepperVariable level) (StepperVariable level)
    -> PureMLPattern level StepperVariable
    -> PureMLPattern level StepperVariable
replacePatternVariables mapping =
    mapPatternVariables
        (\var -> fromMaybe var (Map.lookup var mapping))

addAxiomVariablesAsConfig
    :: MetaOrObject level
    => Set.Set (Variable level)
    -> Map.Map (StepperVariable level) (StepperVariable level)
    -> [StepperVariable level]
    -> Counter (Map.Map (StepperVariable level) (StepperVariable level))
addAxiomVariablesAsConfig _ mapping [] = return mapping
addAxiomVariablesAsConfig
    existingVars mapping (ConfigurationVariable _ : vars)
  =
    addAxiomVariablesAsConfig existingVars mapping vars
addAxiomVariablesAsConfig
    existingVars mapping (var@(AxiomVariable av) : vars)
  =
    case Map.lookup var mapping of
        Just _ -> addAxiomVariablesAsConfig existingVars mapping vars
        Nothing -> do
            newVar <-
                freshVariableSuchThat
                    av
                    ( not . (`Set.member` existingVars) )
            addAxiomVariablesAsConfig
                existingVars
                (Map.insert var (ConfigurationVariable newVar) mapping)
                vars

removeAxiomVariables
    :: MetaOrObject level
    => UnificationSubstitution level StepperVariable
    -> UnificationSubstitution level StepperVariable
removeAxiomVariables =
    filter
        (\ (variable, _) -> case variable of
            AxiomVariable _         -> False
            ConfigurationVariable _ -> True
        )

makeUnifiedSubstitution
    :: MetaOrObject level
    => [(StepperVariable level, PureMLPattern level StepperVariable)]
    -> [(Unified StepperVariable, PureMLPattern level StepperVariable)]
makeUnifiedSubstitution =
    map (Arrow.first asUnified)
