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
    ) where

import qualified Control.Monad as Monad
import           Control.Monad.Except
import           Control.Monad.State
                 ( StateT )
import qualified Control.Monad.State as State
import           Control.Monad.Trans.Except
                 ( throwE )
import           Data.Either
                 ( partitionEithers )
import qualified Data.Hashable as Hashable
import           Data.List
                 ( foldl' )
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
                 ( mapMaybe )
import           Data.Semigroup
                 ( Semigroup (..) )
import           Data.Sequence
                 ( Seq )
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import           GHC.Generics
                 ( Generic )

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Debug
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( Predicate, makeAndPredicate, makeNotPredicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Proof.Functional
                 ( FunctionalProof (..) )
import           Kore.Step.AxiomPatterns
                 ( RewriteRule (RewriteRule), RulePattern (RulePattern) )
import           Kore.Step.AxiomPatterns as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.Error
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, PredicateSubstitution, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.ExpandedPattern as PredicateSubstitution
                 ( toPredicate )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern, OrOfPredicateSubstitution )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns, make, merge, mergeAll )
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
import           Kore.Unification.Data
                 ( UnificationProof (..) )
import           Kore.Unification.Error
                 ( UnificationOrSubstitutionError )
import           Kore.Unification.Procedure
                 ( unificationProcedure )
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
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
    sortedVariableSort =
        \case
            AxiomVariable variable -> variableSort variable
            ConfigurationVariable variable ->
                sortedVariableSort variable
    fromVariable = AxiomVariable

instance
    (FreshVariable variable, SortedVariable variable) =>
    FreshVariable (StepperVariable variable)
  where
    freshVariableWith (AxiomVariable a) n =
        ConfigurationVariable $ freshVariableWith (fromVariable a) n
    freshVariableWith (ConfigurationVariable a) n =
        ConfigurationVariable $ freshVariableWith a n

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
-- 'Kore.Step.Function.Matcher.matchAsUnification' to be used in
-- 'stepWithRule'.
newtype UnificationProcedure level =
    UnificationProcedure
        ( forall variable m
        .   ( SortedVariable variable
            , Ord (variable level)
            , Show (variable level)
            , Unparse (variable level)
            , OrdMetaOrObject variable
            , ShowMetaOrObject variable
            , MetaOrObject level
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
    -> PredicateSubstitutionSimplifier level Simplifier
    -> ExpandedPattern level variable
    -- ^ Configuration being rewritten.
    -> RulePattern level
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
    expandedPattern@Predicated { term = initialTerm }
    axiom@RulePattern { left = axiomLeftRaw }
  = do
    -- Distinguish configuration (pattern) and axiom variables by lifting them
    -- into 'StepperVariable'.
    let
        axiomLeft =
            Kore.Step.Pattern.mapVariables AxiomVariable axiomLeftRaw
        startPattern =
            Kore.Step.Pattern.mapVariables ConfigurationVariable initialTerm

    let
        -- Keep a set of all variables for remapping errors (below).
        existingVars = ExpandedPattern.allVariables expandedPattern

        -- Remap unification and substitution errors into 'StepError'.
        normalizeUnificationOrSubstitutionError
            ::  ( FreshVariable variable
                , MetaOrObject level
                , Ord (variable level)
                , Show (variable level)
                )
            => Set (variable level)
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
    (rawOrPredicateSubstitution, rawSubstitutionProof) <-
        normalizeUnificationOrSubstitutionError
            existingVars
            (unificationProcedure'
                tools
                substitutionSimplifier
                axiomLeft
                startPattern
            )
    keepGoodResults $ return $ map
        (applyUnificationToRhs
            tools
            substitutionSimplifier
            axiom
            existingVars
            expandedPattern
            rawSubstitutionProof
        )
        (OrOfExpandedPattern.extractPatterns rawOrPredicateSubstitution)

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
    -> PredicateSubstitutionSimplifier level Simplifier
    -> RulePattern level
    -> Set (variable level)
    -> ExpandedPattern level variable
    -> UnificationProof level (StepperVariable variable)
    -> PredicateSubstitution level (StepperVariable variable)
    -> ExceptT
        (StepError level variable)
        Simplifier
        ( StepResult level variable
        , StepProof level variable
        )
applyUnificationToRhs
    tools
    substitutionSimplifier
    axiom@RulePattern
        { left = axiomLeftRaw
        , right = axiomRightRaw
        , requires = axiomRequiresRaw
        }
    existingVars
    expandedPattern@Predicated
        {term = initialTerm, substitution = initialSubstitution}
    rawSubstitutionProof
    Predicated {predicate = rawPredicate, substitution = rawSubstitution}
  = do
    let
        -- TODO(virgil): Some of the work is duplicated with the
        -- startPattern = mapVariables ConfigurationVariable initialTerm
        -- statement in the caller (stepWithRule). Should solve
        -- this somehow.
        Predicated
            { predicate = startCondition
            , substitution = startSubstitution
            } =
                ExpandedPattern.mapVariables
                    ConfigurationVariable expandedPattern

        wrapAxiomVariables = Kore.Step.Pattern.mapVariables AxiomVariable
        axiomRight :: StepPattern level (StepperVariable variable)
        axiomRight = wrapAxiomVariables axiomRightRaw
        axiomRequires = Predicate.mapVariables AxiomVariable axiomRequiresRaw
    -- Combine the all the predicates and substitutions generated
    -- above and simplify the result.
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
                        Substitution.modify
                            (filter hasConfigurationVariable)
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
        hasConfigurationVariable :: (StepperVariable variable level, a) -> Bool
        hasConfigurationVariable (AxiomVariable _, _) = False
        hasConfigurationVariable (ConfigurationVariable _, _) = True

    let substitution = Substitution.toMap normalizedSubstitution
    -- Apply substitution to resulting configuration and conditions.
    rawResult <- substitute substitution axiomRight

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
            Set.fromList . mapMaybe toVariable . Map.keys
            $ substitution

    -- Unwrap internal 'StepperVariable's and collect the variable mappings
    -- for the proof.
    (results, variableMapping) <-
        (lift . flip runRemapper existingVars) do
            result <- remapStepPattern rawResult
            condition <- remapPredicate normalizedCondition
            remainderPredicate <- remapPredicate normalizedRemainderPredicate
            substitutionProof <- remapUnificationProof rawSubstitutionProof
            return (result, condition, remainderPredicate, substitutionProof)
    let (result, condition, remainderPredicate, substitutionProof) = results

    let substitutionCoversLeftAxiom =
            variablesInLeftAxiom `Set.isSubsetOf` substitutions
    Monad.unless
        (Predicate.isFalse condition || substitutionCoversLeftAxiom)
        $ error $ unlines
            [ "While applying axiom:"
            , show axiom
            , "to configuration:"
            , show expandedPattern
            , "Unexpected non-false predicate:"
            , show condition
            , "when substitutions:"
            , show substitutions
            , "do not cover all variables in left axiom:"
            , show variablesInLeftAxiom
            ]

    let
        orElse :: a -> a -> a
        p1 `orElse` p2 = if Predicate.isFalse condition then p2 else p1
    return
        ( StepResult
            { rewrittenPattern = Predicated
                { term = result `orElse` mkBottom_
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
                (variablePairToRenaming <$> Map.toList variableMapping)
            )
            ((stepProof . StepProofUnification) substitutionProof)
        )
  where
    variablePairToRenaming
        :: (Variable level, variable level)
        -> VariableRenaming level variable
    variablePairToRenaming (original, renamed) = VariableRenaming
        { variableRenamingOriginal = AxiomVariable original
        , variableRenamingRenamed  = ConfigurationVariable renamed
        }

keepGoodResults
    :: ExceptT
        a
        Simplifier
        [ ExceptT a Simplifier b ]
    -> ExceptT a Simplifier [b]
keepGoodResults mresultsm = do
    resultsm <- mresultsm
    resultsEither <- lift $ mapM runExceptT resultsm
    let
        (errors, goodResults) = partitionEithers resultsEither
    if null goodResults
        then case errors of
            [] -> return []
            (err : _) -> throwE err
        else return goodResults

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
    -> PredicateSubstitutionSimplifier level Simplifier
    -> ExpandedPattern level variable
    -- ^ Configuration being rewritten.
    -> RewriteRule level
    -- ^ Rewriting axiom
    -> ExceptT
        (StepError level variable)
        Simplifier
        [   ( StepResult level variable
            , StepProof level variable
            )
        ]
stepWithRewriteRule tools substitutionSimplifier patt (RewriteRule rule) =
    traceExceptT D_BaseStep_stepWithRule [debugArg "rule" rule] $
    stepWithRule
            tools
            (UnificationProcedure unificationProcedure)
            substitutionSimplifier
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
    -> PredicateSubstitutionSimplifier level Simplifier
    -> [RulePattern level]
    -- ^ Rewriting axiom
    -> ExpandedPattern level variable
    -- ^ Configuration being rewritten.
    -> Simplifier
        ( OrStepResult level variable
        , StepProof level variable
        )
stepWithRemaindersForUnifier
    _
    _
    _
    []
    patt
  = return
    ( OrStepResult
        { rewrittenPattern = OrOfExpandedPattern.make []
        , remainder = OrOfExpandedPattern.make [patt]
        }
    , mempty
    )
stepWithRemaindersForUnifier
    tools
    unification
    substitutionSimplifier
    (rule : rules)
    patt
  = do
    resultsEither <- runExceptT
        $ stepWithRule
            tools
            unification
            substitutionSimplifier
            patt
            rule
    case resultsEither of
        Left _ ->
            stepWithRemaindersForUnifier
                tools unification substitutionSimplifier rules patt
        Right resultsWithProofs -> do
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
                            OrOfExpandedPattern.mergeAll rewritten
                        , remainder = OrOfExpandedPattern.make []
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
                OrOfExpandedPattern.merge firstPattern secondPattern
            , remainder =
                OrOfExpandedPattern.merge firstRemainder secondRemainder
            }
    splitStepResult
        :: StepResult level variable
        ->  ( OrOfExpandedPattern level variable
            , ExpandedPattern level variable
            )
    splitStepResult
        StepResult { rewrittenPattern, remainder }
      =
        ( OrOfExpandedPattern.make [rewrittenPattern]
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
    -> PredicateSubstitutionSimplifier level Simplifier
    -> ExpandedPattern level variable
    -- ^ Configuration being rewritten.
    -> [RewriteRule level]
    -- ^ Rewriting axiom
    -> Simplifier
        ( OrStepResult level variable
        , StepProof level variable
        )
stepWithRemainders tools substitutionSimplifier patt rules =
    stepWithRemaindersForUnifier
        tools
        (UnificationProcedure unificationProcedure)
        substitutionSimplifier
        (map (\ (RewriteRule rule) -> rule) rules)
        patt

configurationVariableToCommon
    :: StepperVariable variable level -> variable level
configurationVariableToCommon (AxiomVariable a) =
    error ("Unexpected AxiomVariable: '" ++ show a ++ "'.")
configurationVariableToCommon (ConfigurationVariable v) = v

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

{- | @Remapper@ carries the context needed to remap 'StepperVariable's.

@Remapper level variable a@ represents a value of type @a@ in the context of a
remapping from @'StepperVariable' variable level@ to @variable level@ which
preserves 'ConfigurationVariable's.

Use 'remapAxiomVariable' to remap a single 'StepperVariable'. Use 'evalRemapper'
to evaluate @Remapper level variable a@ and extract the value @a@ from its
context.

 -}
type Remapper level variable =
    StateT (RemapperState level variable) Simplifier

{- | The context used by 'Remapper'.

The context tracks the mapping from axiom variables to generated variables. The
set of existing configuration variables is used to ensure that generated
variable names do not collide with existing variables. @existingVariables@
includes previously-generated variables.

 -}
data RemapperState level variable =
    RemapperState
        { existingVariables :: !(Set (variable level))
        -- ^ Existing configuration variables
        , mappedVariables :: !(Map (Variable level) (variable level))
        -- ^ Axiom variables already remapped
        }

{- | Evaluate a 'Remapper', extracting the value from its context.

The set of existing configuration variables is used to avoid introducing
internal generated variables whose names collide with external variables.

 -}
evalRemapper
    :: Remapper level variable a
    -> Set (variable level)  -- ^ existing (configuration) variables
    -> Simplifier a
evalRemapper remapper existingVariables = do
    (a, _) <- runRemapper remapper existingVariables
    return a

{- | Evaluate a 'Remapper', extracting the value and mapping from its context.

The set of existing configuration variables is used to avoid introducing
internal generated variables whose names collide with external variables.

The returned mapping records the assignments of all axiom variables which were
remapped.

 -}
runRemapper
    :: Remapper level variable a
    -> Set (variable level)  -- ^ existing (configuration) variables
    -> Simplifier (a, Map (Variable level) (variable level))
runRemapper remapper existingVariables = do
    (a, RemapperState { mappedVariables }) <- State.runStateT remapper state0
    return (a, mappedVariables)
  where
    state0 =
        RemapperState
            { existingVariables
            , mappedVariables = Map.empty
            }

{- | Remap a single 'Variable', returning a generated variable.

The mapping from the original to the generated variable is recorded in the
context. The generated variable will be unique from the existing configuration
variables recorded in the context.

 -}
remapVariable
    ::  ( MetaOrObject level
        , FreshVariable variable
        , SortedVariable variable
        , Ord (variable level)
        )
    => Variable level
    -> Remapper level variable (variable level)
remapVariable variable = do
    RemapperState { existingVariables, mappedVariables } <- State.get
    case Map.lookup variable mappedVariables of
        Just variable' -> return variable'
        Nothing -> do
            variable' <-
                freshVariableSuchThat
                    (fromVariable variable)
                    (`Set.notMember` existingVariables)
            State.put RemapperState
                { existingVariables =
                    Set.insert variable' existingVariables
                , mappedVariables =
                    Map.insert variable variable' mappedVariables
                }
            return variable'

{- | Remap a single 'StepperVariable', returning a configuration variable.

'AxiomVariable's are remapped to generated variables, but
'ConfigurationVariable's are returned unaltered. If a new mapping is generated,
it is recorded in the context.

The remapping functions below are wrappers around @remapAxiomVariable@.

See also: 'remapVariable'

 -}
remapAxiomVariable
    ::  ( MetaOrObject level
        , FreshVariable variable
        , SortedVariable variable
        , Ord (variable level)
        )
    => StepperVariable variable level
    -> Remapper level variable (variable level)
remapAxiomVariable =
    \case
        AxiomVariable var -> remapVariable var
        ConfigurationVariable var -> return var

{- | Remap the 'StepperVariable's in a 'UnificationProof'.

See also: 'remapAxiomVariable'

 -}
remapUnificationProof
    ::  ( MetaOrObject level
        , FreshVariable variable
        , SortedVariable variable
        , Ord (variable level)
        )
    => UnificationProof level (StepperVariable variable)
    -> Remapper level variable (UnificationProof level variable)
remapUnificationProof =
    \case
        EmptyUnificationProof ->
            return EmptyUnificationProof
        CombinedUnificationProof proofs ->
            CombinedUnificationProof <$> traverse remapUnificationProof proofs
        ConjunctionIdempotency patt ->
            ConjunctionIdempotency <$> remapStepPattern patt
        Proposition_5_24_3 functionalProof variable patt ->
            Proposition_5_24_3
                <$> traverse remapFunctionalProof functionalProof
                <*> remapAxiomVariable variable
                <*> remapStepPattern patt
        AndDistributionAndConstraintLifting symbolOrAlias unificationProof ->
            AndDistributionAndConstraintLifting symbolOrAlias
                <$> traverse remapUnificationProof unificationProof
        SubstitutionMerge variable patt1 patt2 ->
            SubstitutionMerge
                <$> remapAxiomVariable variable
                <*> remapStepPattern patt1
                <*> remapStepPattern patt2

{- | Remap the 'StepperVariable's in a 'FunctionalProof'.

See also: 'remapAxiomVariable'

 -}
remapFunctionalProof
    ::  ( MetaOrObject level
        , FreshVariable variable
        , SortedVariable variable
        , Ord (variable level)
        )
    => FunctionalProof level (StepperVariable variable)
    -> Remapper level variable (FunctionalProof level variable)
remapFunctionalProof =
    \case
        FunctionalVariable variable ->
            FunctionalVariable <$> remapAxiomVariable variable
        FunctionalHead f ->
            return (FunctionalHead f)
        FunctionalStringLiteral sl ->
            return (FunctionalStringLiteral sl)
        FunctionalCharLiteral cl ->
            return (FunctionalCharLiteral cl)
        FunctionalDomainValue dv ->
            return (FunctionalDomainValue dv)

{- | Remap the 'StepperVariable's in a 'Predicate'.

See also: 'remapAxiomVariable'

 -}
remapPredicate
    ::  ( MetaOrObject level
        , FreshVariable variable
        , SortedVariable variable
        , Ord (variable level)
        )
    => Predicate level (StepperVariable variable)
    -> Remapper level variable (Predicate level variable)
remapPredicate =
    (traverse . Kore.Step.Pattern.traverseVariables) remapAxiomVariable

{- | Remap the 'StepperVariable's in a 'StepPattern'.

See also: 'remapAxiomVariable'

 -}
remapStepPattern
    ::  ( FreshVariable variable
        , SortedVariable variable
        , MetaOrObject level
        , Ord (variable level)
        )
    => StepPattern level (StepperVariable variable)
    -> Remapper level variable (StepPattern level variable)
remapStepPattern = Kore.Step.Pattern.traverseVariables remapAxiomVariable

{- | Remap the 'StepperVariable's in a 'StepError'.

See also: 'remapAxiomVariable'

 -}
remapStepError
    ::  ( FreshVariable variable
        , SortedVariable variable
        , MetaOrObject level
        , Ord (variable level)
        )
    => StepError level (StepperVariable variable)
    -> Remapper level variable (StepError level variable)
remapStepError = traverseStepErrorVariables remapAxiomVariable

-- | Unwrap 'StepperVariable's so that errors are not expressed in terms of
-- internally-defined variables.
stepperVariableToVariableForError
    ::  ( FreshVariable variable
        , SortedVariable variable
        , MetaOrObject level
        , Ord (variable level)
        )
    => Set (variable level)
    -> ExceptT (StepError level (StepperVariable variable)) Simplifier a
    -> ExceptT (StepError level variable                  ) Simplifier a
stepperVariableToVariableForError existingVars =
    mapExceptT \action ->
        action >>= \case
            Right value -> return (Right value)
            Left err -> Left <$> evalRemapper (remapStepError err) existingVars
