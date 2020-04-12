{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Equation.Application
    ( attemptEquation
    , AttemptEquationResult
    , applyEquationResult
    -- * Errors
    , AttemptEquationError (..)
    , MatchError (..)
    , ApplyMatchResultErrors (..), ApplyMatchResultError (..)
    , CheckRequiresError (..)
    -- * Logging
    , DebugAttemptEquation (..)
    , DebugApplyEquationResult (..)
    , debugApplyEquationResult
    ) where

import Prelude.Kore

import Control.Error
    ( ExceptT
    , MaybeT (..)
    , noteT
    , runExceptT
    , throwE
    , withExceptT
    )
import Control.Monad
    ( (>=>)
    )
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Foldable as Foldable
import Data.List.NonEmpty
    ( NonEmpty (..)
    )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Debug
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Pattern.FreeVariables
    ( HasFreeVariables (..)
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
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
    ( Pattern
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
import Kore.Internal.TermLike
    ( ElementVariable (..)
    , InternalVariable
    , SetVariable (..)
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
import Kore.Syntax.Variable
    ( Variable
    , toVariable
    )
import Kore.TopBottom
import Kore.Unparser
    ( Unparse (..)
    )
import Kore.Variables.Target
    ( Target
    )
import qualified Kore.Variables.Target as Target
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    , mapUnifiedVariable
    )
import Log
    ( Entry (..)
    , MonadLog
    , Severity (..)
    , logEntry
    , logWhile
    )
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

The caller should use 'debugApplyEquationResult' to log when the result of an
equation is actually used; @attemptEquation@ will only log when an equation is
applicable.

 -}
attemptEquation
    :: forall simplifier variable
    .  MonadSimplify simplifier
    => InternalVariable variable
    => SideCondition (Target variable)
    -> TermLike (Target variable)
    -> Equation variable
    -> simplifier (AttemptEquationResult variable)
attemptEquation sideCondition termLike equation =
    whileDebugAttemptEquation' $ runExceptT $ do
        let Equation { left } = equationRenamed
        matchResult <- match left termLike & whileMatch
        (equation', predicate) <-
            applyMatchResult equationRenamed matchResult
            & whileApplyMatchResult
        let Equation { requires } = equation'
        checkRequires sideCondition predicate requires & whileCheckRequires
        let Equation { right, ensures } = equation'
        return $ Pattern.withCondition right $ from @(Predicate _) ensures
  where
    equationRenamed = targetEquationVariables sideCondition termLike equation
    matchError =
        MatchError
        { matchTerm = termLike
        , matchEquation = equationRenamed
        }
    match term1 term2 =
        matchIncremental term1 term2
        & MaybeT & noteT matchError

    whileDebugAttemptEquation'
        :: simplifier (AttemptEquationResult variable)
        -> simplifier (AttemptEquationResult variable)
    whileDebugAttemptEquation' action = do
        result <- whileDebugAttemptEquation termLike equationRenamed action
        debugAttemptEquationResult result
        return result

applyEquationResult
    :: forall simplifier variable
    .  MonadSimplify simplifier
    => InternalVariable variable
    => SideCondition variable
    -> Equation variable
    -> Pattern variable
    -> simplifier (OrPattern variable)
applyEquationResult _ equation result = do
    let results = OrPattern.fromPattern result
    let simplify = return
    debugApplyEquationResult equation result
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
    =>  Equation (Target variable)
    ->  MatchResult (Target variable)
    ->  ExceptT (ApplyMatchResultErrors (Target variable)) monad
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
            Predicate.substitute substitution predicate
            & Predicate.mapVariables Target.unTargetElement Target.unTargetSet
        equation' =
            Equation.substitute substitution equation
            & Equation.mapVariables Target.unTargetElement Target.unTargetSet
    return (equation', predicate')
  where
    equationVariables =
        freeVariables equation
        & FreeVariables.getFreeVariables
        & Set.toList

    errors = concatMap checkVariable equationVariables

    checkVariable variable =
        case Map.lookup variable substitution of
            Nothing -> [NotMatched variable]
            Just termLike ->
                checkConcreteVariable variable termLike
                <> checkSymbolicVariable variable termLike

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

    Equation { attributes } = equation
    concretes =
        attributes
        & Attribute.concrete & Attribute.unConcrete
        & FreeVariables.getFreeVariables
    symbolics =
        attributes
        & Attribute.symbolic & Attribute.unSymbolic
        & FreeVariables.getFreeVariables

{- | Check that the requires from matching and the 'Equation' hold.

Throws 'RequiresNotMet' if the 'Predicate's do not hold under the
'SideCondition'.

 -}
checkRequires
    :: forall simplifier variable
    .  MonadSimplify simplifier
    => InternalVariable variable
    => SideCondition (Target variable)
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
    & (OrCondition.gather >=> assertBottom)
  where
    simplifyCondition = Simplifier.simplifyCondition sideCondition'

    -- TODO (thomas.tuegel): Do not unwrap sideCondition.
    sideCondition' =
        SideCondition.mapVariables
            Target.unTargetElement
            Target.unTargetSet
            sideCondition

    assertBottom orCondition
      | isBottom orCondition = done
      | otherwise            = requiresNotMet
    done = return ()
    requiresNotMet =
        throwE CheckRequiresError
            { matchPredicate = predicate
            , equationRequires = requires
            }

    -- Pair a configuration with sideCondition for evaluation by the solver.
    withSideCondition = (,) sideCondition'

    withoutAxioms =
        fmap Condition.forgetSimplified
        . Simplifier.localSimplifierAxioms (const mempty)
    withAxioms = id

{- | Make the 'Equation' variables distinct from the initial pattern.

The variables are marked 'Target' and renamed to avoid any variables in the
'SideCondition' or the 'TermLike'.

 -}
targetEquationVariables
    :: forall variable
    .  InternalVariable variable
    => SideCondition (Target variable)
    -> TermLike (Target variable)
    -> Equation variable
    -> Equation (Target variable)
targetEquationVariables sideCondition initial =
    snd
    . Equation.refreshVariables avoiding
    . Equation.mapVariables Target.mkElementTarget Target.mkSetTarget
  where
    avoiding = freeVariables sideCondition <> freeVariables initial

-- * Errors

{- | Errors that can occur during 'attemptEquation'.
 -}
data AttemptEquationError variable
    = WhileMatch !(MatchError (Target variable))
    | WhileApplyMatchResult !(ApplyMatchResultErrors (Target variable))
    | WhileCheckRequires !(CheckRequiresError variable)
    deriving (Eq, Ord)
    deriving (GHC.Generic)

mapAttemptEquationErrorVariables
    :: (InternalVariable variable1, InternalVariable variable2)
    => (ElementVariable variable1 -> ElementVariable variable2)
    -> (SetVariable     variable1 -> SetVariable     variable2)
    -> AttemptEquationError variable1
    -> AttemptEquationError variable2
mapAttemptEquationErrorVariables mapElemVar mapSetVar =
    \case
        WhileMatch matchError ->
            WhileMatch
            $ mapMatchErrorVariables
                mapElemTargetVar mapSetTargetVar
                matchError
        WhileApplyMatchResult applyMatchResultErrors ->
            WhileApplyMatchResult
            $ mapApplyMatchResultErrorsVariables
                mapElemTargetVar mapSetTargetVar
                applyMatchResultErrors
        WhileCheckRequires checkRequiresError ->
            WhileCheckRequires
            $ mapCheckRequiresErrorVariables
                mapElemVar mapSetVar
                checkRequiresError
  where
    mapElemTargetVar =
        ElementVariable
        . fmap (getElementVariable . mapElemVar . ElementVariable)
        . getElementVariable
    mapSetTargetVar =
        SetVariable
        . fmap (getSetVariable . mapSetVar . SetVariable)
        . getSetVariable

whileMatch
    :: Functor monad
    => ExceptT (MatchError (Target variable)) monad a
    -> ExceptT (AttemptEquationError variable) monad a
whileMatch = withExceptT WhileMatch

whileApplyMatchResult
    :: Functor monad
    => ExceptT (ApplyMatchResultErrors (Target variable)) monad a
    -> ExceptT (AttemptEquationError variable) monad a
whileApplyMatchResult = withExceptT WhileApplyMatchResult

whileCheckRequires
    :: Functor monad
    => ExceptT (CheckRequiresError variable) monad a
    -> ExceptT (AttemptEquationError variable) monad a
whileCheckRequires = withExceptT WhileCheckRequires

instance SOP.Generic (AttemptEquationError variable)

instance SOP.HasDatatypeInfo (AttemptEquationError variable)

instance Debug variable => Debug (AttemptEquationError variable)

instance (Debug variable, Diff variable) => Diff (AttemptEquationError variable)

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
    deriving (Eq, Ord)
    deriving (GHC.Generic)

instance SOP.Generic (MatchError variable)

instance SOP.HasDatatypeInfo (MatchError variable)

instance Debug variable => Debug (MatchError variable)

instance (Debug variable, Diff variable) => Diff (MatchError variable)

instance InternalVariable variable => Pretty (MatchError variable) where
    pretty MatchError { matchTerm, matchEquation } =
        Pretty.vsep
        [ "could not match term:"
        , Pretty.indent 4 (unparse matchTerm)
        , "with equation:"
        , Pretty.indent 4 (pretty matchEquation)
        ]

mapMatchErrorVariables
    :: (InternalVariable variable1, InternalVariable variable2)
    => (ElementVariable variable1 -> ElementVariable variable2)
    -> (SetVariable     variable1 -> SetVariable     variable2)
    -> MatchError variable1
    -> MatchError variable2
mapMatchErrorVariables mapElemVar mapSetVar =
    \MatchError { matchTerm, matchEquation } ->
        MatchError
        { matchTerm = TermLike.mapVariables mapElemVar mapSetVar matchTerm
        , matchEquation =
            Equation.mapVariables mapElemVar mapSetVar matchEquation
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
    deriving (Eq, Ord)
    deriving (GHC.Generic)

instance SOP.Generic (ApplyMatchResultErrors variable)

instance SOP.HasDatatypeInfo (ApplyMatchResultErrors variable)

instance Debug variable => Debug (ApplyMatchResultErrors variable)

instance
    (Debug variable, Diff variable)
    => Diff (ApplyMatchResultErrors variable)

instance
    InternalVariable variable
    => Pretty (ApplyMatchResultErrors variable)
  where
    pretty ApplyMatchResultErrors { applyMatchErrors } =
        Pretty.vsep
        [ "could not apply match result due to errors:"
        , (Pretty.indent 4 . Pretty.vsep)
            (pretty <$> Foldable.toList applyMatchErrors)
        ]

mapApplyMatchResultErrorsVariables
    :: (InternalVariable variable1, InternalVariable variable2)
    => (ElementVariable variable1 -> ElementVariable variable2)
    -> (SetVariable     variable1 -> SetVariable     variable2)
    -> ApplyMatchResultErrors variable1
    -> ApplyMatchResultErrors variable2
mapApplyMatchResultErrorsVariables mapElemVar mapSetVar applyMatchResultErrors =
    ApplyMatchResultErrors
    { matchResult = mapMatchResultVariables mapElemVar mapSetVar matchResult
    , applyMatchErrors =
        fmap
            (mapApplyMatchResultErrorVariables mapElemVar mapSetVar)
            applyMatchErrors
    }
  where
    ApplyMatchResultErrors { matchResult, applyMatchErrors } =
        applyMatchResultErrors

mapMatchResultVariables
    :: (InternalVariable variable1, InternalVariable variable2)
    => (ElementVariable variable1 -> ElementVariable variable2)
    -> (SetVariable     variable1 -> SetVariable     variable2)
    -> MatchResult variable1
    -> MatchResult variable2
mapMatchResultVariables mapElemVar mapSetVar (predicate, substitution) =
    ( Predicate.mapVariables mapElemVar mapSetVar predicate
    , mapSubstitutionVariables substitution
    )
  where
    mapSubstitutionVariables =
       Map.mapKeys (mapUnifiedVariable mapElemVar mapSetVar)
       . Map.map (TermLike.mapVariables mapElemVar mapSetVar)

{- | @ApplyMatchResultError@ represents a reason the match could not be applied.
 -}
data ApplyMatchResultError variable
    = NotConcrete (UnifiedVariable variable) (TermLike variable)
    -- ^ The variable was matched with a symbolic term where a concrete
    -- term was required.
    | NotSymbolic (UnifiedVariable variable) (TermLike variable)
    -- ^ The variable was matched with a concrete term where a symbolic
    -- term was required.
    | NotMatched (UnifiedVariable variable)
    -- ^ The variable was not matched.
    deriving (Eq, Ord)
    deriving (GHC.Generic)

instance SOP.Generic (ApplyMatchResultError variable)

instance SOP.HasDatatypeInfo (ApplyMatchResultError variable)

instance Debug variable => Debug (ApplyMatchResultError variable)

instance
    (Debug variable, Diff variable)
    => Diff (ApplyMatchResultError variable)

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

mapApplyMatchResultErrorVariables
    :: (InternalVariable variable1, InternalVariable variable2)
    => (ElementVariable variable1 -> ElementVariable variable2)
    -> (SetVariable     variable1 -> SetVariable     variable2)
    -> ApplyMatchResultError variable1
    -> ApplyMatchResultError variable2
mapApplyMatchResultErrorVariables mapElemVar mapSetVar applyMatchResultError =
    case applyMatchResultError of
        NotConcrete variable termLike ->
            NotConcrete
                (mapUnifiedVariable' variable)
                (mapTermLikeVariables termLike)
        NotSymbolic variable termLike ->
            NotSymbolic
                (mapUnifiedVariable' variable)
                (mapTermLikeVariables termLike)
        NotMatched variable -> NotMatched (mapUnifiedVariable' variable)
  where
    mapUnifiedVariable' = mapUnifiedVariable mapElemVar mapSetVar
    mapTermLikeVariables = TermLike.mapVariables mapElemVar mapSetVar

{- | Errors that can occur during 'checkRequires'.
 -}
data CheckRequiresError variable =
    CheckRequiresError
    { matchPredicate :: !(Predicate variable)
    , equationRequires :: !(Predicate variable)
    }
    deriving (Eq, Ord)
    deriving (GHC.Generic)

instance SOP.Generic (CheckRequiresError variable)

instance SOP.HasDatatypeInfo (CheckRequiresError variable)

instance Debug variable => Debug (CheckRequiresError variable)

instance (Debug variable, Diff variable) => Diff (CheckRequiresError variable)

instance InternalVariable variable => Pretty (CheckRequiresError variable) where
    pretty CheckRequiresError { matchPredicate, equationRequires } =
        Pretty.vsep
        [ "could not infer the equation requirement:"
        , Pretty.indent 4 (unparse equationRequires)
        , "and the matching requirement:"
        , Pretty.indent 4 (unparse matchPredicate)
        ]

mapCheckRequiresErrorVariables
    :: (InternalVariable variable1, InternalVariable variable2)
    => (ElementVariable variable1 -> ElementVariable variable2)
    -> (SetVariable     variable1 -> SetVariable     variable2)
    -> CheckRequiresError variable1
    -> CheckRequiresError variable2
mapCheckRequiresErrorVariables mapElemVar mapSetVar checkRequiresError =
    CheckRequiresError
    { matchPredicate = mapPredicateVariables matchPredicate
    , equationRequires = mapPredicateVariables equationRequires
    }
  where
    mapPredicateVariables = Predicate.mapVariables mapElemVar mapSetVar
    CheckRequiresError { matchPredicate, equationRequires } = checkRequiresError

-- * Logging

{- | Log entries for all phases of equation application.
 -}
data DebugAttemptEquation
    = DebugAttemptEquation (TermLike Variable) (Equation Variable)
    -- ^ Covers the entire scope of 'attemptEquation'.
    | DebugAttemptEquationResult (AttemptEquationResult Variable)
    -- ^ Entered into the log when an equation is applicable.
    deriving (GHC.Generic)

instance Pretty DebugAttemptEquation where
    pretty (DebugAttemptEquation termLike equation) =
        Pretty.vsep
        [ "applying equation:"
        , Pretty.indent 4 (pretty equation)
        , "to term:"
        , Pretty.indent 4 (unparse termLike)
        ]
    pretty (DebugAttemptEquationResult (Left attemptEquationError)) =
        Pretty.vsep
        [ "equation is not applicable:"
        , pretty attemptEquationError
        ]
    pretty (DebugAttemptEquationResult (Right result)) =
        Pretty.vsep
        [ "equation is applicable with result:"
        , Pretty.indent 4 (unparse result)
        ]

instance Entry DebugAttemptEquation where
    entrySeverity _ = Debug
    shortDoc _ = Just "while applying equation"

{- | Log the result of attempting to apply an 'Equation'.

 -}
debugAttemptEquationResult
    :: MonadLog log
    => InternalVariable variable
    => AttemptEquationResult variable
    -> log ()
debugAttemptEquationResult =
    logEntry
    . DebugAttemptEquationResult
    . mapAttemptEquationResultVariables toElementVariable toSetVariable
  where
    toElementVariable = fmap toVariable
    toSetVariable = fmap toVariable

mapAttemptEquationResultVariables
    :: (InternalVariable variable1, InternalVariable variable2)
    => (ElementVariable variable1 -> ElementVariable variable2)
    -> (SetVariable     variable1 -> SetVariable     variable2)
    -> AttemptEquationResult variable1
    -> AttemptEquationResult variable2
mapAttemptEquationResultVariables mapElemVar mapSetVar =
    Bifunctor.bimap
        (mapAttemptEquationErrorVariables mapElemVar mapSetVar)
        (Pattern.mapVariables mapElemVar mapSetVar)

whileDebugAttemptEquation
    :: MonadLog log
    => InternalVariable variable
    => TermLike variable
    -> Equation variable
    -> log a
    -> log a
whileDebugAttemptEquation termLike equation =
    logWhile (DebugAttemptEquation termLike' equation')
  where
    toElementVariable = fmap toVariable
    toSetVariable = fmap toVariable
    termLike' = TermLike.mapVariables toElementVariable toSetVariable termLike
    equation' = Equation.mapVariables toElementVariable toSetVariable equation

{- | Log when an 'Equation' is actually applied.
 -}
data DebugApplyEquationResult
    = DebugApplyEquationResult (Equation Variable) (Pattern Variable)
    -- ^ Entered into the log when an equation's result is actually used.
    deriving (GHC.Generic)

instance Pretty DebugApplyEquationResult where
    pretty (DebugApplyEquationResult equation result) =
        Pretty.vsep
        [ "applied equation:"
        , Pretty.indent 4 (pretty equation)
        , "with result:"
        , Pretty.indent 4 (unparse result)
        ]

instance Entry DebugApplyEquationResult where
    entrySeverity _ = Debug

{- | Log when an 'Equation' is actually applied.

@debugApplyEquationResult@ is different from 'debugAttemptEquationResult', which
only indicates if an equation is applicable, that is: if it could apply. If
multiple equations are applicable in the same place, the caller will determine
which is actually applied. Therefore, the /caller/ should use this log entry
after 'attemptEquation'.

 -}
debugApplyEquationResult
    :: MonadLog log
    => InternalVariable variable
    => Equation variable
    -> Pattern variable
    -> log ()
debugApplyEquationResult equation result =
    logEntry $ DebugApplyEquationResult equation' result'
  where
    toElementVariable = fmap toVariable
    toSetVariable = fmap toVariable
    equation' = Equation.mapVariables toElementVariable toSetVariable equation
    result' = Pattern.mapVariables toElementVariable toSetVariable result
