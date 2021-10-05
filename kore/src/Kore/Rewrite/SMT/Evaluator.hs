{- |
Module      : Kore.Rewrite.SMT.Evaluator
Description : Uses a SMT solver for evaluating predicates.
Copyright   : (c) Runtime Verification, 2018-2019-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
-}
module Kore.Rewrite.SMT.Evaluator (
    decidePredicate,
    evalPredicate,
    evalConditional,
    evalPredicateWithSideCondition,
    evalConditionalWithSideCondition,
    filterMultiOr,
    translateTerm,
    translatePredicate,
) where

import Control.Error (
    MaybeT,
    runMaybeT,
 )
import qualified Control.Lens as Lens
import qualified Control.Monad.Counter as Counter
import qualified Control.Monad.State.Strict as State
import Data.Generics.Product.Fields
import qualified Data.Map.Strict as Map
import Data.Reflection
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import qualified Kore.Attribute.Symbol as Attribute (
    Symbol,
 )
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional (
    Conditional,
 )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.MultiOr (
    MultiOr,
 )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.Predicate (
    Predicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike (
    ElementVariable,
    ElementVariableName,
    SomeVariableName,
    Variable (..),
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Log.DebugEvaluateCondition (
    debugEvaluateConditionResult,
    whileDebugEvaluateCondition,
 )
import Kore.Log.ErrorDecidePredicateUnknown (
    errorDecidePredicateUnknown,
 )
import Kore.Log.WarnRetrySolverQuery (
    warnRetrySolverQuery,
 )
import Kore.Rewrite.SMT.Translate
import Kore.Simplify.Simplify as Simplifier
import Kore.TopBottom (
    TopBottom,
 )
import Log
import Prelude.Kore
import Pretty (
    Pretty,
 )
import qualified Pretty
import SMT (
    Result (..),
    SExpr (..),
 )
import qualified SMT
import qualified SMT.SimpleSMT as SimpleSMT

-- | Attempt to evaluate the 'Predicate' argument using an external SMT solver.
evalPredicate ::
    MonadSimplify m =>
    InternalVariable variable =>
    Predicate variable ->
    m (Maybe Bool)
evalPredicate = \case
    Predicate.PredicateTrue -> return $ Just True
    Predicate.PredicateFalse -> return $ Just False
    predicate ->
        predicate :| []
            & decidePredicate SideCondition.top

{- | Attempt to evaluate the 'Predicate' argument with 'SideCondition' using
 an external SMT solver.
-}
evalPredicateWithSideCondition ::
    MonadSimplify m =>
    InternalVariable variable =>
    Predicate variable ->
    SideCondition variable ->
    m (Maybe Bool)
evalPredicateWithSideCondition predicate sideCondition = case predicate of
    Predicate.PredicateTrue -> return $ Just True
    Predicate.PredicateFalse -> return $ Just False
    _ ->
        predicate :| [from @_ @(Predicate _) sideCondition]
            & decidePredicate sideCondition

{- | Attempt to evaluate the 'Conditional' argument using an external SMT
 solver.
-}
evalConditional ::
    MonadSimplify m =>
    InternalVariable variable =>
    Conditional variable term ->
    m (Maybe Bool)
evalConditional conditional =
    evalPredicate (Conditional.predicate conditional)
        & assert (Conditional.isNormalized conditional)

{- | Attempt to evaluate the 'Conditional' argument with 'SideCondition'
 using an external SMT solver.
-}
evalConditionalWithSideCondition ::
    MonadSimplify m =>
    InternalVariable variable =>
    Conditional variable term ->
    SideCondition variable ->
    m (Maybe Bool)
evalConditionalWithSideCondition conditional sideCondition =
    evalPredicateWithSideCondition (Condition.toPredicate condition) sideCondition
        & assert (Conditional.isNormalized conditional)
  where
    condition = Conditional.withoutTerm conditional

-- | Removes from a MultiOr all items refuted by an external SMT solver.
filterMultiOr ::
    forall simplifier term variable.
    ( MonadSimplify simplifier
    , Ord term
    , TopBottom term
    , InternalVariable variable
    ) =>
    MultiOr (Conditional variable term) ->
    simplifier (MultiOr (Conditional variable term))
filterMultiOr multiOr = do
    elements <- mapM refute $ toList multiOr
    return $ MultiOr.make $ catMaybes elements
  where
    refute ::
        Conditional variable term ->
        simplifier (Maybe (Conditional variable term))
    refute p =
        evalConditional p <&> \case
            Nothing -> Just p
            Just False -> Nothing
            Just True -> Just p

{- | Attempt to refute a predicate using an external SMT solver.

The predicate is always sent to the external solver, even if it is trivial.
-}
decidePredicate ::
    forall variable simplifier.
    InternalVariable variable =>
    MonadSimplify simplifier =>
    SideCondition variable ->
    NonEmpty (Predicate variable) ->
    simplifier (Maybe Bool)
decidePredicate sideCondition predicates =
    whileDebugEvaluateCondition predicates go
  where
    go =
        do
            result <- query >>= whenUnknown retry
            debugEvaluateConditionResult result
            case result of
                Unsat -> return False
                Sat -> empty
                Unknown ->
                    errorDecidePredicateUnknown predicates
            & runMaybeT

    whenUnknown f Unknown = f
    whenUnknown _ result = return result
    query :: MaybeT simplifier Result
    query =
        SMT.withSolver . evalTranslator $ do
            tools <- Simplifier.askMetadataTools
            predicates' <-
                traverse
                    (translatePredicate sideCondition tools)
                    predicates
            traverse_ SMT.assert predicates'
            SMT.check

    retry = do
        SMT.reinit
        result <- query
        warnRetrySolverQuery predicates
        return result

translatePredicate ::
    forall variable m.
    ( InternalVariable variable
    , SMT.MonadSMT m
    , MonadLog m
    ) =>
    SideCondition variable ->
    SmtMetadataTools Attribute.Symbol ->
    Predicate variable ->
    Translator variable m SExpr
translatePredicate sideCondition tools predicate =
    give tools $
        translatePredicateWith sideCondition translateTerm predicate

translateTerm ::
    forall m variable.
    InternalVariable variable =>
    SMT.MonadSMT m =>
    MonadLog m =>
    -- | type name
    SExpr ->
    -- | uninterpreted pattern
    TranslateItem variable ->
    Translator variable m SExpr
translateTerm smtType (QuantifiedVariable var) = do
    n <- Counter.increment
    let varName = "<" <> Text.pack (show n) <> ">"
        smtVar = SimpleSMT.const varName
    field @"quantifiedVars"
        Lens.%= Map.insert
            var
            SMTDependentAtom
                { smtName = varName
                , smtType
                , boundVars = []
                }
    return smtVar
translateTerm t (UninterpretedTerm (TermLike.ElemVar_ var)) =
    lookupVariable var <|> declareVariable t var
translateTerm t (UninterpretedPredicate predicate) = do
    TranslatorState{quantifiedVars, predicates} <- State.get
    let freeVars = FreeVariables.freeVariableNames @_ @variable predicate
        boundVarsMap = filterBoundVarsMap freeVars quantifiedVars
        boundPat =
            Predicate.makeExistsPredicateN (Map.keys boundVarsMap) predicate
        stateSetter = field @"predicates"
    lookupUninterpreted boundPat quantifiedVars predicates
        <|> declareUninterpreted t stateSetter boundPat boundVarsMap
translateTerm t (UninterpretedTerm pat) = do
    TranslatorState{quantifiedVars, terms} <- State.get
    let freeVars = FreeVariables.freeVariableNames @_ @variable pat
        boundVarsMap = filterBoundVarsMap freeVars quantifiedVars
        boundPat = TermLike.mkExistsN (Map.keys boundVarsMap) pat
        stateSetter = field @"terms"
    lookupUninterpreted boundPat quantifiedVars terms
        <|> declareUninterpreted t stateSetter boundPat boundVarsMap

declareUninterpreted ::
    ( MonadSMT m
    , MonadLog m
    , InternalVariable variable
    , Ord termOrPredicate
    , Pretty termOrPredicate
    ) =>
    SExpr ->
    Lens.ASetter'
        (TranslatorState variable)
        (Map.Map termOrPredicate (SMTDependentAtom variable)) ->
    termOrPredicate ->
    Map.Map (ElementVariable variable) (SMTDependentAtom variable) ->
    Translator variable m SExpr
declareUninterpreted
    sExpr
    stateSetter
    boundPat
    boundVarsMap =
        do
            n <- Counter.increment
            logVariableAssignment n boundPat
            let smtName = "<" <> Text.pack (show n) <> ">"
                (boundVars, bindings) = unzip $ Map.assocs boundVarsMap
                cached = SMTDependentAtom{smtName, smtType = sExpr, boundVars}
            _ <-
                SMT.declareFun
                    SMT.FunctionDeclaration
                        { name = Atom smtName
                        , inputSorts = smtType <$> bindings
                        , resultSort = sExpr
                        }
            stateSetter Lens.%= Map.insert boundPat cached
            translateSMTDependentAtom boundVarsMap cached

filterBoundVarsMap ::
    Ord variable =>
    Set.Set (SomeVariableName variable) ->
    Map.Map
        (Variable (ElementVariableName variable))
        (SMTDependentAtom variable) ->
    Map.Map
        (Variable (ElementVariableName variable))
        (SMTDependentAtom variable)
filterBoundVarsMap freeVars quantifiedVars =
    Map.filterWithKey
        (\k _ -> inject (variableName k) `Set.member` freeVars)
        quantifiedVars

lookupUninterpreted ::
    (InternalVariable variable, MonadSMT m, Ord k) =>
    k ->
    Map.Map (ElementVariable variable) (SMTDependentAtom variable) ->
    Map.Map k (SMTDependentAtom variable) ->
    Translator variable m SExpr
lookupUninterpreted boundPat quantifiedVars terms =
    maybe empty (translateSMTDependentAtom quantifiedVars) $
        Map.lookup boundPat terms

lookupVariable ::
    InternalVariable variable =>
    Monad m =>
    TermLike.ElementVariable variable ->
    Translator variable m SExpr
lookupVariable var =
    lookupQuantifiedVariable <|> lookupFreeVariable
  where
    lookupQuantifiedVariable = do
        TranslatorState{quantifiedVars} <- State.get
        maybeToTranslator $
            SMT.Atom . smtName <$> Map.lookup var quantifiedVars
    lookupFreeVariable = do
        TranslatorState{freeVars} <- State.get
        maybeToTranslator $ Map.lookup var freeVars

declareVariable ::
    InternalVariable variable =>
    SMT.MonadSMT m =>
    MonadLog m =>
    -- | type name
    SExpr ->
    -- | variable to be declared
    TermLike.ElementVariable variable ->
    Translator variable m SExpr
declareVariable t variable = do
    n <- Counter.increment
    let varName = "<" <> Text.pack (show n) <> ">"
    var <- SMT.declare varName t
    field @"freeVars" Lens.%= Map.insert variable var
    logVariableAssignment n (TermLike.mkElemVar variable)
    return var

logVariableAssignment ::
    Pretty pretty =>
    MonadLog m =>
    Counter.Natural ->
    -- | variable to be declared
    pretty ->
    Translator variable m ()
logVariableAssignment n pat =
    logDebug
        . Text.pack
        . show
        . Pretty.nest 4
        . Pretty.sep
        $ [Pretty.pretty n, "|->", Pretty.pretty pat]
