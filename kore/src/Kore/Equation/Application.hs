{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

{-# LANGUAGE Strict #-}
module Kore.Equation.Application
    ( attemptEquation
    , AttemptEquationResult
    , applyEquation
    , applySubstitutionAndSimplify
    -- * Errors
    , AttemptEquationError (..)
    , MatchError (..)
    , ApplyMatchResultErrors (..), ApplyMatchResultError (..)
    , CheckRequiresError (..)
    -- * Logging
    , DebugAttemptEquation (..)
    , DebugApplyEquation (..)
    , debugApplyEquation
    ) where

import Prelude.Kore

import Control.Error
    ( ExceptT
    , MaybeT (..)
    , maybeToList
    , noteT
    , runExceptT
    , throwE
    , withExceptT
    )
import Control.Monad
    ( (>=>)
    )
import Control.Monad.Except
    ( catchError
    )
import qualified Data.Bifunctor as Bifunctor
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Debug
import Kore.AST.AstWithLocation
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Pattern.FreeVariables
    ( HasFreeVariables (..)
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import qualified Kore.Attribute.Source as Attribute
import Kore.Equation.Equation
    ( Equation (..)
    )
import qualified Kore.Equation.Equation as Equation
import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Conditional (..)
    , Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    , makeAndPredicate
    , makeNotPredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.Substitution
    ( Substitution
    )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
    ( InternalVariable
    , TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Step.Axiom.Matcher
    ( MatchResult
    , matchIncremental
    )
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    )
import qualified Kore.Step.Simplification.Simplify as Simplifier
import qualified Kore.Step.SMT.Evaluator as SMT
import qualified Kore.Step.Substitution as Substitution
import Kore.Syntax.Id
    ( AstLocation (..)
    , FileLocation (..)
    )
import Kore.Syntax.Variable
import Kore.TopBottom
import Kore.Unparser
    ( Unparse (..)
    )
import Log
    ( Entry (..)
    , MonadLog
    , Severity (..)
    , logEntry
    , logWhile
    )
import qualified Logic
import Pretty
    ( Pretty (..)
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
attemptEquation
    :: forall simplifier variable
    .  HasCallStack
    => MonadSimplify simplifier
    => InternalVariable variable
    => SideCondition variable
    -> TermLike variable
    -> Equation variable
    -> simplifier (AttemptEquationResult variable)
attemptEquation sideCondition termLike equation =
    whileDebugAttemptEquation' $ runExceptT $ do
        let Equation { left, argument, antiLeft } = equationRenamed
        (equation', predicate) <- matchAndApplyResults left argument antiLeft
        let Equation { requires } = equation'
        checkRequires sideCondition predicate requires & whileCheckRequires
        let Equation { right, ensures } = equation'
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
        & MaybeT & noteT matchError

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

    applyAndSelectMatchResult
        :: [MatchResult variable]
        -> ExceptT
            (AttemptEquationError variable)
            simplifier
            (Equation variable, Predicate variable)
    applyAndSelectMatchResult [] =
        throwE (WhileMatch matchError)
    applyAndSelectMatchResult results =
        whileApplyMatchResult $ foldr1
            takeFirstSuccess
            (applyMatchResult equationRenamed <$> results)
    takeFirstSuccess first second = catchError first (const second)

    whileDebugAttemptEquation'
        :: simplifier (AttemptEquationResult variable)
        -> simplifier (AttemptEquationResult variable)
    whileDebugAttemptEquation' action =
        whileDebugAttemptEquation termLike equationRenamed $ do
            result <- action
            debugAttemptEquationResult equation result
            return result

-- | Simplify the argument of a function definition equation with the
-- match substitution and the priority predicate. This will avoid
-- evaluating any function applications or builtins present in
-- the predicates. It will not attempt any user defined simplification rules
-- either.
applySubstitutionAndSimplify
    :: HasCallStack
    => MonadSimplify simplifier
    => InternalVariable variable
    => Maybe (Predicate variable)
    -> Maybe (Predicate variable)
    -> Map (SomeVariableName variable) (TermLike variable)
    -> ExceptT
        (MatchError variable)
        simplifier
        [MatchResult variable]
applySubstitutionAndSimplify
    argument
    antiLeft
    matchSubstitution
  =
    lift . Simplifier.localSimplifierAxioms mempty $ do
        let toMatchResult Conditional { predicate, substitution } =
                (predicate, Substitution.toMap substitution)
        Substitution.mergePredicatesAndSubstitutions
            SideCondition.top
            (maybeToList argument <> maybeToList antiLeft)
            [from @_ @(Substitution _) matchSubstitution]
            & Logic.observeAllT
            & (fmap . fmap) toMatchResult

applyEquation
    :: forall simplifier variable
    .  MonadSimplify simplifier
    => InternalVariable variable
    => SideCondition variable
    -> Equation variable
    -> Pattern variable
    -> simplifier (OrPattern variable)
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
applyMatchResult
    :: forall monad variable
    .   Monad monad
    =>  InternalVariable variable
    =>  Equation variable
    ->  MatchResult variable
    ->  ExceptT (ApplyMatchResultErrors variable) monad
            (Equation variable, Predicate variable)
applyMatchResult equation matchResult@(predicate, substitution) = do
    case errors of
        x : xs ->
            throwE ApplyMatchResultErrors
                { matchResult
                , applyMatchErrors = x :| xs
                }
        _      -> return ()
    let predicate' =
            Predicate.substitute orientedSubstitution predicate
        equation' =
            Equation.substitute orientedSubstitution equation
    return (equation', predicate')
  where
    orientedSubstitution = Substitution.orientSubstitution occursInEquation substitution

    equationVariables = freeVariables equation

    occursInEquation :: (SomeVariableName variable -> Bool)
    occursInEquation = \someVariableName ->
        Set.member someVariableName equationVariableNames

    equationVariableNames =
        Set.map variableName (FreeVariables.toSet equationVariables)

    errors =
        concatMap checkVariable (FreeVariables.toList equationVariables)
        <> checkNotInEquation

    checkVariable Variable { variableName } =
        case Map.lookup variableName orientedSubstitution of
            Nothing -> [NotMatched variableName]
            Just termLike ->
                checkConcreteVariable variableName termLike
                <> checkSymbolicVariable variableName termLike

    checkConcreteVariable variable termLike
      | Set.member variable concretes
      , (not . TermLike.isConstructorLike) termLike
      = [NotConcrete variable termLike]
      | otherwise
      = empty

    checkSymbolicVariable variable termLike
      | Set.member variable symbolics
      , TermLike.isConstructorLike termLike
      = [NotSymbolic variable termLike]
      | otherwise
      = empty

    checkNotInEquation =
        NonMatchingSubstitution
        <$> filter (not . occursInEquation) (Map.keys orientedSubstitution)

    Equation { attributes } = equation
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
checkRequires
    :: forall simplifier variable
    .  MonadSimplify simplifier
    => InternalVariable variable
    => SideCondition variable
    -> Predicate variable  -- ^ requires from matching
    -> Predicate variable  -- ^ requires from 'Equation'
    -> ExceptT (CheckRequiresError variable) simplifier ()
checkRequires sideCondition predicate requires =
    do
        let requires' = makeAndPredicate predicate requires
            -- The condition to refute:
            condition :: Condition variable
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

    assertBottom orCondition
      | isBottom orCondition = done
      | otherwise            = requiresNotMet
    done = return ()
    requiresNotMet =
        throwE CheckRequiresError
            { matchPredicate = predicate
            , equationRequires = requires
            , sideCondition
            }

    -- Pair a configuration with sideCondition for evaluation by the solver.
    withSideCondition = (,) sideCondition

    withoutAxioms =
        fmap Condition.forgetSimplified
        . Simplifier.localSimplifierAxioms (const mempty)
    withAxioms = id

refreshVariables
    :: forall variable
    .  InternalVariable variable
    => SideCondition variable
    -> TermLike variable
    -> Equation variable
    -> Equation variable
refreshVariables sideCondition initial =
    snd
    . Equation.refreshVariables avoiding
  where
    avoiding = sideConditionVariables <> freeVariables initial
    sideConditionVariables = freeVariables sideCondition

-- * Errors

{- | Errors that can occur during 'attemptEquation'.
 -}
data AttemptEquationError variable
    = WhileMatch !(MatchError variable)
    | WhileApplyMatchResult !(ApplyMatchResultErrors variable)
    | WhileCheckRequires !(CheckRequiresError variable)
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

mapAttemptEquationErrorVariables
    :: (InternalVariable variable1, InternalVariable variable2)
    => AdjSomeVariableName (variable1 -> variable2)
    -> AttemptEquationError variable1
    -> AttemptEquationError variable2
mapAttemptEquationErrorVariables adj =
    \case
        WhileMatch matchError ->
            WhileMatch $ mapMatchErrorVariables adj matchError
        WhileApplyMatchResult applyMatchResultErrors ->
            WhileApplyMatchResult
            $ mapApplyMatchResultErrorsVariables
                adj
                applyMatchResultErrors
        WhileCheckRequires checkRequiresError ->
            WhileCheckRequires
            $ mapCheckRequiresErrorVariables adj checkRequiresError

whileMatch
    :: Functor monad
    => ExceptT (MatchError variable) monad a
    -> ExceptT (AttemptEquationError variable) monad a
whileMatch = withExceptT WhileMatch

whileApplyMatchResult
    :: Functor monad
    => ExceptT (ApplyMatchResultErrors variable) monad a
    -> ExceptT (AttemptEquationError variable) monad a
whileApplyMatchResult = withExceptT WhileApplyMatchResult

whileCheckRequires
    :: Functor monad
    => ExceptT (CheckRequiresError variable) monad a
    -> ExceptT (AttemptEquationError variable) monad a
whileCheckRequires = withExceptT WhileCheckRequires

instance
    InternalVariable variable
    => Pretty (AttemptEquationError variable)
  where
    pretty (WhileMatch matchError) =
        pretty matchError
    pretty (WhileApplyMatchResult applyMatchResultErrors) =
        pretty applyMatchResultErrors
    pretty (WhileCheckRequires checkRequiresError) =
        pretty checkRequiresError

{- | Errors that can occur while matching the equation to the term.
 -}
data MatchError variable =
    MatchError
    { matchTerm :: !(TermLike variable)
    , matchEquation :: !(Equation variable)
    }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance InternalVariable variable => Pretty (MatchError variable) where
    pretty _ = "equation did not match term"

mapMatchErrorVariables
    :: (InternalVariable variable1, InternalVariable variable2)
    => AdjSomeVariableName (variable1 -> variable2)
    -> MatchError variable1
    -> MatchError variable2
mapMatchErrorVariables adj =
    \MatchError { matchTerm, matchEquation } ->
        MatchError
        { matchTerm = TermLike.mapVariables adj matchTerm
        , matchEquation = Equation.mapVariables adj matchEquation
        }

{- | Errors that can occur during 'applyMatchResult'.

There may be multiple independent reasons the match cannot be applied, so this
type contains a 'NonEmpty' list of 'ApplyMatchError'.

 -}
data ApplyMatchResultErrors variable =
    ApplyMatchResultErrors
    { matchResult :: !(MatchResult variable)
    , applyMatchErrors :: !(NonEmpty (ApplyMatchResultError variable))
    }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance
    InternalVariable variable
    => Pretty (ApplyMatchResultErrors variable)
  where
    pretty ApplyMatchResultErrors { applyMatchErrors } =
        Pretty.vsep
        [ "could not apply match result:"
        , (Pretty.indent 4 . Pretty.vsep)
            (pretty <$> toList applyMatchErrors)
        ]

mapApplyMatchResultErrorsVariables
    :: (InternalVariable variable1, InternalVariable variable2)
    => AdjSomeVariableName (variable1 -> variable2)
    -> ApplyMatchResultErrors variable1
    -> ApplyMatchResultErrors variable2
mapApplyMatchResultErrorsVariables adj applyMatchResultErrors =
    ApplyMatchResultErrors
    { matchResult = mapMatchResultVariables adj matchResult
    , applyMatchErrors =
        mapApplyMatchResultErrorVariables adj <$> applyMatchErrors
    }
  where
    ApplyMatchResultErrors { matchResult, applyMatchErrors } =
        applyMatchResultErrors

mapMatchResultVariables
    :: (InternalVariable variable1, InternalVariable variable2)
    => AdjSomeVariableName (variable1 -> variable2)
    -> MatchResult variable1
    -> MatchResult variable2
mapMatchResultVariables adj (predicate, substitution) =
    ( Predicate.mapVariables adj predicate
    , mapSubstitutionVariables substitution
    )
  where
    mapSubstitutionVariables =
       Map.mapKeys (mapSomeVariableName adj)
       . Map.map (TermLike.mapVariables adj)

{- | @ApplyMatchResultError@ represents a reason the match could not be applied.
 -}
data ApplyMatchResultError variable
    = NotConcrete (SomeVariableName variable) (TermLike variable)
    -- ^ The variable was matched with a symbolic term where a concrete
    -- term was required.
    | NotSymbolic (SomeVariableName variable) (TermLike variable)
    -- ^ The variable was matched with a concrete term where a symbolic
    -- term was required.
    | NotMatched (SomeVariableName variable)
    -- ^ The variable was not matched.
    | NonMatchingSubstitution (SomeVariableName variable)
    -- ^ The variable is not part of the matching solution.
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance
    InternalVariable variable
    => Pretty (ApplyMatchResultError variable)
  where
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

mapApplyMatchResultErrorVariables
    :: (InternalVariable variable1, InternalVariable variable2)
    => AdjSomeVariableName (variable1 -> variable2)
    -> ApplyMatchResultError variable1
    -> ApplyMatchResultError variable2
mapApplyMatchResultErrorVariables adj applyMatchResultError =
    case applyMatchResultError of
        NotConcrete variable termLike ->
            NotConcrete
                (mapSomeVariableName' variable)
                (mapTermLikeVariables termLike)
        NotSymbolic variable termLike ->
            NotSymbolic
                (mapSomeVariableName' variable)
                (mapTermLikeVariables termLike)
        NotMatched variable -> NotMatched (mapSomeVariableName' variable)
        NonMatchingSubstitution variable ->
            NonMatchingSubstitution (mapSomeVariableName' variable)
  where
    mapSomeVariableName' = mapSomeVariableName adj
    mapTermLikeVariables = TermLike.mapVariables adj

{- | Errors that can occur during 'checkRequires'.
 -}
data CheckRequiresError variable =
    CheckRequiresError
    { matchPredicate :: !(Predicate variable)
    , equationRequires :: !(Predicate variable)
    , sideCondition :: !(SideCondition variable)
    }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance InternalVariable variable => Pretty (CheckRequiresError variable) where
    pretty checkRequiresError =
        Pretty.vsep
        [ "could not infer the equation requirement:"
        , Pretty.indent 4 (pretty equationRequires)
        , "and the matching requirement:"
        , Pretty.indent 4 (pretty matchPredicate)
        , "from the side condition:"
        , Pretty.indent 4 (pretty sideCondition)
        ]
      where
        CheckRequiresError { matchPredicate, equationRequires, sideCondition } =
            checkRequiresError

mapCheckRequiresErrorVariables
    :: (InternalVariable variable1, InternalVariable variable2)
    => AdjSomeVariableName (variable1 -> variable2)
    -> CheckRequiresError variable1
    -> CheckRequiresError variable2
mapCheckRequiresErrorVariables adj checkRequiresError =
    CheckRequiresError
    { matchPredicate = mapPredicateVariables matchPredicate
    , equationRequires = mapPredicateVariables equationRequires
    , sideCondition = SideCondition.mapVariables adj sideCondition
    }
  where
    mapPredicateVariables = Predicate.mapVariables adj
    CheckRequiresError { matchPredicate, equationRequires, sideCondition } =
        checkRequiresError

-- * Logging

{- | Log entries for all phases of equation application.
 -}
data DebugAttemptEquation
    = DebugAttemptEquation (Equation VariableName) (TermLike VariableName)
    -- ^ Covers the entire scope of 'attemptEquation'.
    | DebugAttemptEquationResult
        (Equation VariableName)
        (AttemptEquationResult VariableName)
    -- ^ Entered into the log when an equation is applicable.
    deriving (Show)
    deriving (GHC.Generic)

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
    shortDoc (DebugAttemptEquation equation _) =
        (Just . Pretty.hsep . catMaybes)
            [ Just "while applying equation"
            , (\loc -> Pretty.hsep ["at", pretty loc]) <$> srcLoc equation
            ]
    shortDoc _ = Nothing
    helpDoc _ = "log equation application attempts"

{- | Log the result of attempting to apply an 'Equation'.

 -}
debugAttemptEquationResult
    :: MonadLog log
    => InternalVariable variable
    => Equation variable
    -> AttemptEquationResult variable
    -> log ()
debugAttemptEquationResult equation result =
    logEntry $ DebugAttemptEquationResult
        (Equation.mapVariables (pure toVariableName) equation)
        (mapAttemptEquationResultVariables (pure toVariableName) result)

mapAttemptEquationResultVariables
    :: (InternalVariable variable1, InternalVariable variable2)
    => AdjSomeVariableName (variable1 -> variable2)
    -> AttemptEquationResult variable1
    -> AttemptEquationResult variable2
mapAttemptEquationResultVariables adj =
    Bifunctor.bimap
        (mapAttemptEquationErrorVariables adj)
        (Pattern.mapVariables adj)

whileDebugAttemptEquation
    :: MonadLog log
    => InternalVariable variable
    => TermLike variable
    -> Equation variable
    -> log a
    -> log a
whileDebugAttemptEquation termLike equation =
    logWhile (DebugAttemptEquation equation' termLike')
  where
    termLike' = TermLike.mapVariables (pure toVariableName) termLike
    equation' = Equation.mapVariables (pure toVariableName) equation

{- | Log when an 'Equation' is actually applied.
 -}
data DebugApplyEquation
    = DebugApplyEquation (Equation VariableName) (Pattern VariableName)
    -- ^ Entered into the log when an equation's result is actually used.
    deriving (Show)
    deriving (GHC.Generic)

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

srcLoc :: Equation VariableName -> Maybe Attribute.SourceLocation
srcLoc equation
  | (not . isLocEmpty) kLoc = Just kLoc
  | AstLocationFile fileLocation <- locationFromAst equation =
    Just (from @FileLocation fileLocation)
  | otherwise = Nothing
  where
    kLoc = Attribute.sourceLocation $ attributes equation

isLocEmpty :: Attribute.SourceLocation -> Bool
isLocEmpty Attribute.SourceLocation { source = Attribute.Source file } =
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
debugApplyEquation
    :: MonadLog log
    => InternalVariable variable
    => Equation variable
    -> Pattern variable
    -> log ()
debugApplyEquation equation result =
    logEntry $ DebugApplyEquation equation' result'
  where
    equation' = Equation.mapVariables (pure toVariableName) equation
    result' = Pattern.mapVariables (pure toVariableName) result
