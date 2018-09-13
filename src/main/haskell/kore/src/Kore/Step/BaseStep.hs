{-|
Module      : Kore.Step.BaseStep
Description : Single step execution
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.BaseStep
    ( AxiomPattern (..)
    , StepperConfiguration (..)
    , StepperVariable (..)
    , stepWithAxiom
    ) where

import qualified Control.Arrow as Arrow
import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe )
import           Data.Monoid
                 ( (<>) )
import           Data.Reflection
                 ( Given, give )
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
                 ( Predicate, makeFalsePredicate,
                 makeMultipleAndPredicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.AxiomPatterns
import           Kore.Step.Error
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern),
                 PredicateSubstitution (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Substitution
                 ( mergeAndNormalizeSubstitutions )
import           Kore.Substitution.Class
                 ( Hashable (..), PatternSubstitutionClass (..) )
import qualified Kore.Substitution.List as ListSubstitution
import           Kore.Unification.Error
                 ( UnificationError, ctorSubstitutionCycleToBottom )
import           Kore.Unification.Unifier
                 ( UnificationSubstitution,
                 mapSubstitutionVariables, unificationProcedure )
import           Kore.Variables.Free
                 ( pureAllVariables )
import           Kore.Variables.Fresh.Class
                 ( FreshVariablesClass (freshVariableSuchThat) )
import           Kore.Variables.Fresh.IntCounter
                 ( IntCounter )
import           Kore.Variables.Int
                 ( IntVariable (..) )
{-| 'StepperConfiguration' represents the configuration to which a rewriting
axiom is applied.

A configuration consists of a pattern and a condition predicate, and would be
represented as pattern /\ condition-predicate in Kore.
--}
data StepperConfiguration level = StepperConfiguration
    { stepperConfigurationPattern       :: !(CommonPurePattern level KoreDomain)
    -- ^ The pattern being rewritten.

    , stepperConfigurationCondition     :: !(CommonPurePattern level KoreDomain)
    -- ^ The condition predicate.
    -- TODO(virgil): Make this an EvaluatedCondition.
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

instance IntVariable StepperVariable where
    intVariable (AxiomVariable a) n = AxiomVariable (intVariable a n)
    intVariable (ConfigurationVariable a) n =
        ConfigurationVariable (intVariable a n)

getStepperVariableVariable :: StepperVariable level -> Variable level
getStepperVariableVariable (AxiomVariable a)         = a
getStepperVariableVariable (ConfigurationVariable a) = a

{-| 'stepWithAxiom' executes a single rewriting step using the provided axiom.

Does not handle properly various cases, among which:
sigma(x, y) => y    vs    a

TODO: Decide if Left here also includes bottom results or only impossibilities.
-}
stepWithAxiom
    ::  ( MetaOrObject level )
    => MetadataTools level StepperAttributes
    -> ExpandedPattern.CommonExpandedPattern level domain
    -- ^ Configuration being rewritten.
    -> AxiomPattern level domain
    -- ^ Rewriting axiom
    -> Either
        (IntCounter (StepError level Variable))
        (IntCounter
            (ExpandedPattern.CommonExpandedPattern level domain, ())
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
            -> Either (IntCounter (StepError level Variable)) a
        normalizeUnificationError bottom existingVariables action =
            stepperVariableToVariableForError
                existingVariables (unificationToStepError bottom action)

    -- Unify the left-hand side of the rewriting axiom with the initial
    -- configuration, producing a substitution (instantiating the axiom to the
    -- configuration) subject to a predicate.
    (     unificationSubstitution
        , unificationCondition
        , _
        ) <-
            normalizeUnificationError
                ([], makeFalsePredicate, ())
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
            $ ctorSubstitutionCycleToBottom
            ( return ( PredicateSubstitution
                           { predicate = makeFalsePredicate
                           , substitution = []
                           }
                     , ()
                     )
            )
            $ mergeAndNormalizeSubstitutions tools unificationSubstitution startSubstitution

    return $ do
        ( PredicateSubstitution
              { predicate = normalizedCondition
              , substitution = normalizedSubstitution
              }
          , ()
          ) <- normalizedSubstitutionWithCounter

        let
            unifiedSubstitution =
                ListSubstitution.fromList
                    (makeUnifiedSubstitution normalizedSubstitution)
        -- Merge all conditions collected so far
            (mergedConditionWithCounter, ()) = 
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
        (_variableMapping1, condition) <-
            predicateStepVariablesToCommon
                existingVars variableMapping rawCondition
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
            , ()
            )
  where
    -- | Unwrap 'StepperVariable's so that errors are not expressed in terms of
    -- internally-defined variables.
    stepperVariableToVariableForError
        :: MetaOrObject level
        => Set.Set (Variable level)
        -> Either (StepError level StepperVariable) a
        -> Either (IntCounter (StepError level Variable)) a
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

mergeConditionsWithAnd
    ::  ( MetaOrObject level
        , Given (SortTools level)
        , SortedVariable var
        , Show (var level))
    => [Predicate level domain var]
    -> (IntCounter (Predicate level domain var), ())
mergeConditionsWithAnd conditions =
    let
        (predicate, _) = makeMultipleAndPredicate conditions
    in
        (return predicate, ())


predicateStepVariablesToCommon
    :: MetaOrObject level
    => Set.Set (Variable level)
    -> Map.Map (StepperVariable level) (StepperVariable level)
    -> Predicate level domain StepperVariable
    -> IntCounter
        ( Map.Map (StepperVariable level) (StepperVariable level)
        , Predicate level domain Variable
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
    -> PureMLPattern level domain StepperVariable
    -> IntCounter
        ( Map.Map (StepperVariable level) (StepperVariable level)
        , PureMLPattern level domain Variable
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
    -> PureMLPattern level domain StepperVariable
    -> PureMLPattern level domain StepperVariable
replacePatternVariables mapping =
    mapPatternVariables
        (\var -> fromMaybe var (Map.lookup var mapping))

addAxiomVariablesAsConfig
    :: MetaOrObject level
    => Set.Set (Variable level)
    -> Map.Map (StepperVariable level) (StepperVariable level)
    -> [StepperVariable level]
    -> IntCounter (Map.Map (StepperVariable level) (StepperVariable level))
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
    => UnificationSubstitution level domain StepperVariable
    -> UnificationSubstitution level domain StepperVariable
removeAxiomVariables =
    filter
        (\ (variable, _) -> case variable of
            AxiomVariable _         -> False
            ConfigurationVariable _ -> True
        )

makeUnifiedSubstitution
    :: MetaOrObject level
    => [(StepperVariable level, PureMLPattern level domain StepperVariable)]
    -> [(Unified StepperVariable, PureMLPattern level domain StepperVariable)]
makeUnifiedSubstitution =
    map (Arrow.first asUnified)
