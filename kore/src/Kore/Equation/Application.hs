{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Kore.Equation.Application (
    attemptEquation,
    AttemptEquationResult,
    applyEquation,
    applySubstitutionAndSimplify,

    -- * Errors
    AttemptEquationError (..),
    MatchError (..),
    ApplyMatchResultErrors (..),
    ApplyMatchResultError (..),
    CheckRequiresError (..),

    -- * Logging
    DebugAttemptEquation (..),
    DebugApplyEquation (..),
    debugApplyEquation,
) where

import Control.Error (
    ExceptT,
    MaybeT (..),
    maybeToList,
    noteT,
    runExceptT,
    throwE,
    withExceptT,
 )
import Control.Monad (
    (>=>),
 )
import Control.Monad.Except (
    catchError,
 )
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import Data.Set (
    Set,
 )
import qualified Data.Set as Set
import Debug
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.AST.AstWithLocation
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Pattern.FreeVariables (
    HasFreeVariables (..),
 )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import qualified Kore.Attribute.Source as Attribute
import Kore.Equation.Equation (
    Equation (..),
 )
import qualified Kore.Equation.Equation as Equation
import Kore.Internal.Condition (
    Condition,
 )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.OrCondition (
    OrCondition,
 )
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Conditional (..),
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    Predicate,
    makeAndPredicate,
    makeNotPredicate,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.Substitution (
    Substitution,
 )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike (
    TermLike,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Step.Axiom.Matcher (
    MatchResult,
    matchIncremental,
 )
import qualified Kore.Step.SMT.Evaluator as SMT
import Kore.Step.Simplification.Simplify (
    MonadSimplify,
 )
import qualified Kore.Step.Simplification.Simplify as Simplifier
import qualified Kore.Step.Substitution as Substitution
import Kore.Substitute
import Kore.Syntax.Id (
    AstLocation (..),
    FileLocation (..),
 )
import Kore.Syntax.Variable
import Kore.TopBottom
import Kore.Unparser (
    Unparse (..),
 )
import Log (
    Entry (..),
    MonadLog,
    Severity (..),
    logEntry,
    logWhile,
 )
import qualified Logic
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import qualified Pretty

{- | The outcome of an attempt to apply an 'Equation'.

@AttemptEquationResult@ is 'Right' if the equation is applicable, and 'Left'
otherwise. If the equation is not applicable, the 'AttemptEquationError' will
indicate the reason.
-}
type AttemptEquationResult variable =
    Either (AttemptEquationError variable) (Pattern variable)

{- | Attempt to apply an 'Equation' to the 'TermLike'.

The 'SideCondition' is used to evaluate the 'requires' clause of the 'Equation'.

The caller should use 'debugApplyEquation' to log when the result of an
equation is actually used; @attemptEquation@ will only log when an equation is
applicable.
-}
attemptEquation ::
    forall simplifier.
    HasCallStack =>
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    TermLike RewritingVariableName ->
    Equation RewritingVariableName ->
    simplifier (AttemptEquationResult RewritingVariableName)
attemptEquation sideCondition termLike equation =
    whileDebugAttemptEquation' . runExceptT $ do
        let Equation{left, argument, antiLeft} = equationRenamed
        (equation', predicate) <- matchAndApplyResults left argument antiLeft
        let Equation{requires} = equation'
        checkRequires sideCondition predicate requires & whileCheckRequires
        let Equation{right, ensures} = equation'
        return $ Pattern.withCondition right $ from @(Predicate _) ensures
  where
    equationRenamed = refreshVariables sideCondition termLike equation
    matchError =
        MatchError
            { matchTerm = termLike
            , matchEquation = equationRenamed
            }
    match term1 term2 =
        matchIncremental sideCondition term1 term2
            & MaybeT
            & noteT matchError

    matchAndApplyResults left' argument' antiLeft'
        | isNothing argument'
          , isNothing antiLeft' = do
            matchResult <- match left' termLike & whileMatch
            applyMatchResult equationRenamed matchResult
                & whileApplyMatchResult
        | otherwise = do
            (matchPredicate, matchSubstitution) <-
                match left' termLike
                    & whileMatch
            matchResults <-
                applySubstitutionAndSimplify
                    argument'
                    antiLeft'
                    matchSubstitution
                    & whileMatch
            (equation', predicate) <-
                applyAndSelectMatchResult matchResults
            return
                ( equation'
                , makeAndPredicate predicate matchPredicate
                )

    applyAndSelectMatchResult ::
        [MatchResult RewritingVariableName] ->
        ExceptT
            (AttemptEquationError RewritingVariableName)
            simplifier
            (Equation RewritingVariableName, Predicate RewritingVariableName)
    applyAndSelectMatchResult [] =
        throwE (WhileMatch matchError)
    applyAndSelectMatchResult results =
        whileApplyMatchResult $
            foldr1
                takeFirstSuccess
                (applyMatchResult equationRenamed <$> results)
    takeFirstSuccess first second = catchError first (const second)

    whileDebugAttemptEquation' ::
        simplifier (AttemptEquationResult RewritingVariableName) ->
        simplifier (AttemptEquationResult RewritingVariableName)
    whileDebugAttemptEquation' action =
        whileDebugAttemptEquation termLike equationRenamed $ do
            result <- action
            debugAttemptEquationResult equation result
            return result

{- | Simplify the argument of a function definition equation with the
 match substitution and the priority predicate. This will avoid
 evaluating any function applications or builtins present in
 the predicates. It will not attempt any user defined simplification rules
 either.
-}
applySubstitutionAndSimplify ::
    HasCallStack =>
    MonadSimplify simplifier =>
    Maybe (Predicate RewritingVariableName) ->
    Maybe (Predicate RewritingVariableName) ->
    Map
        (SomeVariableName RewritingVariableName)
        (TermLike RewritingVariableName) ->
    ExceptT
        (MatchError RewritingVariableName)
        simplifier
        [MatchResult RewritingVariableName]
applySubstitutionAndSimplify
    argument
    antiLeft
    matchSubstitution =
        lift . Simplifier.localSimplifierAxioms mempty $ do
            let toMatchResult Conditional{predicate, substitution} =
                    (predicate, Substitution.toMap substitution)
            Substitution.mergePredicatesAndSubstitutions
                SideCondition.top
                (maybeToList argument <> maybeToList antiLeft)
                [from @_ @(Substitution _) matchSubstitution]
                & Logic.observeAllT
                & (fmap . fmap) toMatchResult

applyEquation ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Equation RewritingVariableName ->
    Pattern RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
applyEquation _ equation result = do
    let results = OrPattern.fromPattern result
    let simplify = return
    debugApplyEquation equation result
    simplify results

{- | Use a 'MatchResult' to instantiate an 'Equation'.

The 'MatchResult' must cover all the free variables of the 'Equation'; this
condition is not checked, but enforced by the matcher. The result is the
'Equation' and any 'Predicate' assembled during matching, both instantiated by
the 'MatchResult'.

Throws 'ApplyMatchResultErrors' if there is a problem with the 'MatchResult'.
-}
applyMatchResult ::
    forall monad.
    Monad monad =>
    Equation RewritingVariableName ->
    MatchResult RewritingVariableName ->
    ExceptT
        (ApplyMatchResultErrors RewritingVariableName)
        monad
        (Equation RewritingVariableName, Predicate RewritingVariableName)
applyMatchResult equation matchResult@(predicate, substitution) = do
    case errors of
        x : xs ->
            throwE
                ApplyMatchResultErrors
                    { matchResult
                    , applyMatchErrors = x :| xs
                    }
        _ -> return ()
    let predicate' = substitute orientedSubstitution predicate
        equation' = substitute orientedSubstitution equation
    return (equation', predicate')
  where
    orientedSubstitution = Substitution.orientSubstitution occursInEquation substitution

    equationVariables = freeVariables equation

    occursInEquation :: (SomeVariableName RewritingVariableName -> Bool)
    occursInEquation = \someVariableName ->
        Set.member someVariableName equationVariableNames

    equationVariableNames =
        Set.map variableName (FreeVariables.toSet equationVariables)

    errors =
        concatMap checkVariable (FreeVariables.toList equationVariables)
            <> checkNotInEquation

    checkVariable Variable{variableName} =
        case Map.lookup variableName orientedSubstitution of
            Nothing -> [NotMatched variableName]
            Just termLike ->
                checkConcreteVariable variableName termLike
                    <> checkSymbolicVariable variableName termLike

    checkConcreteVariable variable termLike
        | Set.member variable concretes
          , (not . TermLike.isConstructorLike) termLike =
            [NotConcrete variable termLike]
        | otherwise =
            empty

    checkSymbolicVariable variable termLike
        | Set.member variable symbolics
          , TermLike.isConstructorLike termLike =
            [NotSymbolic variable termLike]
        | otherwise =
            empty

    checkNotInEquation =
        NonMatchingSubstitution
            <$> filter (not . occursInEquation) (Map.keys orientedSubstitution)

    Equation{attributes} = equation
    concretes =
        attributes
            & Attribute.concrete
            & from @_ @(Set _)
    symbolics =
        attributes
            & Attribute.symbolic
            & from @_ @(Set _)

{- | Check that the requires from matching and the 'Equation' hold.

Throws 'RequiresNotMet' if the 'Predicate's do not hold under the
'SideCondition'.
-}
checkRequires ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    -- | requires from matching
    Predicate RewritingVariableName ->
    -- | requires from 'Equation'
    Predicate RewritingVariableName ->
    ExceptT (CheckRequiresError RewritingVariableName) simplifier ()
checkRequires sideCondition predicate requires =
    do
        let requires' = makeAndPredicate predicate requires
            -- The condition to refute:
            condition :: Condition RewritingVariableName
            condition = from @(Predicate _) (makeNotPredicate requires')
        return condition
            -- First try to refute 'condition' without user-defined axioms:
            >>= withoutAxioms . simplifyCondition
            -- Next try to refute 'condition' including user-defined axioms:
            >>= withAxioms . simplifyCondition
            -- Finally, try to refute the simplified 'condition' using the
            -- external solver:
            >>= SMT.filterBranch . withSideCondition
            >>= return . snd
        -- Collect the simplified results. If they are \bottom, then \and(predicate,
        -- requires) is valid; otherwise, the required pre-conditions are not met
        -- and the rule will not be applied.
        & (OrCondition.observeAllT >=> assertBottom)
  where
    simplifyCondition = Simplifier.simplifyCondition sideCondition

    assertBottom negatedImplication
        | isBottom negatedImplication = done
        | otherwise = requiresNotMet negatedImplication
    done = return ()
    requiresNotMet negatedImplication =
        throwE
            CheckRequiresError
                { matchPredicate = predicate
                , equationRequires = requires
                , sideCondition
                , negatedImplication
                }

    -- Pair a configuration with sideCondition for evaluation by the solver.
    withSideCondition = (,) sideCondition

    withoutAxioms =
        fmap Condition.forgetSimplified
            . Simplifier.localSimplifierAxioms (const mempty)
    withAxioms = id

refreshVariables ::
    SideCondition RewritingVariableName ->
    TermLike RewritingVariableName ->
    Equation RewritingVariableName ->
    Equation RewritingVariableName
refreshVariables sideCondition initial =
    snd
        . Equation.refreshVariables avoiding
  where
    avoiding = sideConditionVariables <> freeVariables initial
    sideConditionVariables = freeVariables sideCondition
-- * Errors

-- | Errors that can occur during 'attemptEquation'.
data AttemptEquationError variable
    = WhileMatch !(MatchError variable)
    | WhileApplyMatchResult !(ApplyMatchResultErrors variable)
    | WhileCheckRequires !(CheckRequiresError variable)
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

whileMatch ::
    Functor monad =>
    ExceptT (MatchError RewritingVariableName) monad a ->
    ExceptT (AttemptEquationError RewritingVariableName) monad a
whileMatch = withExceptT WhileMatch

whileApplyMatchResult ::
    Functor monad =>
    ExceptT (ApplyMatchResultErrors RewritingVariableName) monad a ->
    ExceptT (AttemptEquationError RewritingVariableName) monad a
whileApplyMatchResult = withExceptT WhileApplyMatchResult

whileCheckRequires ::
    Functor monad =>
    ExceptT (CheckRequiresError RewritingVariableName) monad a ->
    ExceptT (AttemptEquationError RewritingVariableName) monad a
whileCheckRequires = withExceptT WhileCheckRequires

instance Pretty (AttemptEquationError RewritingVariableName) where
    pretty (WhileMatch matchError) =
        pretty matchError
    pretty (WhileApplyMatchResult applyMatchResultErrors) =
        pretty applyMatchResultErrors
    pretty (WhileCheckRequires checkRequiresError) =
        pretty checkRequiresError

-- | Errors that can occur while matching the equation to the term.
data MatchError variable = MatchError
    { matchTerm :: !(TermLike variable)
    , matchEquation :: !(Equation variable)
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Pretty (MatchError RewritingVariableName) where
    pretty _ = "equation did not match term"

{- | Errors that can occur during 'applyMatchResult'.

There may be multiple independent reasons the match cannot be applied, so this
type contains a 'NonEmpty' list of 'ApplyMatchError'.
-}
data ApplyMatchResultErrors variable = ApplyMatchResultErrors
    { matchResult :: !(MatchResult variable)
    , applyMatchErrors :: !(NonEmpty (ApplyMatchResultError variable))
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Pretty (ApplyMatchResultErrors RewritingVariableName) where
    pretty ApplyMatchResultErrors{applyMatchErrors} =
        Pretty.vsep
            [ "could not apply match result:"
            , (Pretty.indent 4 . Pretty.vsep)
                (pretty <$> toList applyMatchErrors)
            ]

-- | @ApplyMatchResultError@ represents a reason the match could not be applied.
data ApplyMatchResultError variable
    = -- | The variable was matched with a symbolic term where a concrete
      -- term was required.
      NotConcrete (SomeVariableName variable) (TermLike variable)
    | -- | The variable was matched with a concrete term where a symbolic
      -- term was required.
      NotSymbolic (SomeVariableName variable) (TermLike variable)
    | -- | The variable was not matched.
      NotMatched (SomeVariableName variable)
    | -- | The variable is not part of the matching solution.
      NonMatchingSubstitution (SomeVariableName variable)
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Pretty (ApplyMatchResultError RewritingVariableName) where
    pretty (NotConcrete variable _) =
        Pretty.hsep
            [ "variable"
            , unparse variable
            , "did not match a concrete term"
            ]
    pretty (NotSymbolic variable _) =
        Pretty.hsep
            [ "variable"
            , unparse variable
            , "did not match a symbolic term"
            ]
    pretty (NotMatched variable) =
        Pretty.hsep ["variable", unparse variable, "was not matched"]
    pretty (NonMatchingSubstitution variable) =
        Pretty.hsep
            [ "variable"
            , unparse variable
            , "should not be substituted"
            ]

-- | Errors that can occur during 'checkRequires'.
data CheckRequiresError variable = CheckRequiresError
    { matchPredicate :: !(Predicate variable)
    , equationRequires :: !(Predicate variable)
    , sideCondition :: !(SideCondition variable)
    , negatedImplication :: !(OrCondition variable)
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Pretty (CheckRequiresError RewritingVariableName) where
    pretty checkRequiresError =
        Pretty.vsep
            [ "Could not infer the equation requirement:"
            , Pretty.indent 4 (pretty equationRequires)
            , "and the matching requirement:"
            , Pretty.indent 4 (pretty matchPredicate)
            , "from the side condition:"
            , Pretty.indent 4 (pretty sideCondition)
            , "The negated implication is:"
            , Pretty.indent 4 (pretty negatedImplication)
            ]
      where
        CheckRequiresError
            { matchPredicate
            , equationRequires
            , sideCondition
            , negatedImplication
            } = checkRequiresError

-- * Logging

-- | Log entries for all phases of equation application.
data DebugAttemptEquation
    = -- | Covers the entire scope of 'attemptEquation'.
      DebugAttemptEquation
        (Equation RewritingVariableName)
        (TermLike RewritingVariableName)
    | -- | Entered into the log when an equation is applicable.
      DebugAttemptEquationResult
        (Equation RewritingVariableName)
        (AttemptEquationResult RewritingVariableName)
    deriving stock (Show)
    deriving stock (GHC.Generic)

instance Pretty DebugAttemptEquation where
    pretty (DebugAttemptEquation equation termLike) =
        Pretty.vsep
            [ (Pretty.hsep . catMaybes)
                [ Just "applying equation"
                , (\loc -> Pretty.hsep ["at", pretty loc]) <$> srcLoc equation
                , Just "to term:"
                ]
            , Pretty.indent 4 (unparse termLike)
            ]
    pretty (DebugAttemptEquationResult _ (Left attemptEquationError)) =
        Pretty.vsep
            [ "equation is not applicable:"
            , pretty attemptEquationError
            ]
    pretty (DebugAttemptEquationResult _ (Right _)) =
        "equation is applicable"

instance Entry DebugAttemptEquation where
    entrySeverity _ = Debug
    contextDoc (DebugAttemptEquation equation _) =
        (Just . Pretty.hsep . catMaybes)
            [ Just "while applying equation"
            , (\loc -> Pretty.hsep ["at", pretty loc]) <$> srcLoc equation
            ]
    contextDoc _ = Nothing
    helpDoc _ = "log equation application attempts"
    oneLineDoc (DebugAttemptEquation equation _) =
        (\loc -> Pretty.hsep ["applying equation at", pretty loc])
            <$> srcLoc equation
    oneLineDoc (DebugAttemptEquationResult _ (Left _)) = Just "equation is not applicable"
    oneLineDoc (DebugAttemptEquationResult _ (Right _)) = Just "equation is applicable"

-- | Log the result of attempting to apply an 'Equation'.
debugAttemptEquationResult ::
    MonadLog log =>
    Equation RewritingVariableName ->
    AttemptEquationResult RewritingVariableName ->
    log ()
debugAttemptEquationResult equation result =
    logEntry $ DebugAttemptEquationResult equation result

whileDebugAttemptEquation ::
    MonadLog log =>
    TermLike RewritingVariableName ->
    Equation RewritingVariableName ->
    log a ->
    log a
whileDebugAttemptEquation termLike equation =
    logWhile (DebugAttemptEquation equation termLike)

-- | Log when an 'Equation' is actually applied.
data DebugApplyEquation
    = -- | Entered into the log when an equation's result is actually used.
      DebugApplyEquation
        (Equation RewritingVariableName)
        (Pattern RewritingVariableName)
    deriving stock (Show)
    deriving stock (GHC.Generic)

instance Pretty DebugApplyEquation where
    pretty (DebugApplyEquation equation result) =
        Pretty.vsep
            [ (Pretty.hsep . catMaybes)
                [ Just "applied equation"
                , (\loc -> Pretty.hsep ["at", pretty loc]) <$> srcLoc equation
                , Just "with result:"
                ]
            , Pretty.indent 4 (unparse result)
            ]

srcLoc :: Equation RewritingVariableName -> Maybe Attribute.SourceLocation
srcLoc equation
    | (not . isLocEmpty) kLoc = Just kLoc
    | AstLocationFile fileLocation <- locationFromAst equation =
        Just (from @FileLocation fileLocation)
    | otherwise = Nothing
  where
    kLoc = Attribute.sourceLocation $ attributes equation

isLocEmpty :: Attribute.SourceLocation -> Bool
isLocEmpty Attribute.SourceLocation{source = Attribute.Source file} =
    isNothing file

instance Entry DebugApplyEquation where
    entrySeverity _ = Debug
    helpDoc _ = "log equation application successes"

{- | Log when an 'Equation' is actually applied.

@debugApplyEquation@ is different from 'debugAttemptEquationResult', which
only indicates if an equation is applicable, that is: if it could apply. If
multiple equations are applicable in the same place, the caller will determine
which is actually applied. Therefore, the /caller/ should use this log entry
after 'attemptEquation'.
-}
debugApplyEquation ::
    MonadLog log =>
    Equation RewritingVariableName ->
    Pattern RewritingVariableName ->
    log ()
debugApplyEquation equation result =
    logEntry $ DebugApplyEquation equation result
