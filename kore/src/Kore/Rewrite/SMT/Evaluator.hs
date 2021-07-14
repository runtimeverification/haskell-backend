{- |
Module      : Kore.Rewrite.SMT.Evaluator
Description : Uses a SMT solver for evaluating predicates.
Copyright   : (c) Runtime Verification, 2018-2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
-}
module Kore.Rewrite.SMT.Evaluator (
    decidePredicate,
    Evaluable (..),
    filterBranch,
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
    TermLike,
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
import Kore.Unparser
import Log
import Logic (
    LogicT,
 )
import Prelude.Kore
import qualified Pretty
import SMT (
    Result (..),
    SExpr (..),
 )
import qualified SMT
import qualified SMT.SimpleSMT as SimpleSMT

{- | Class for things that can be evaluated with an SMT solver,
or which contain things that can be evaluated with an SMT solver.
-}
class Evaluable thing where
    -- | Attempt to evaluate the argument with an external SMT solver.
    evaluate :: MonadSimplify m => thing -> m (Maybe Bool)

instance InternalVariable variable => Evaluable (Predicate variable) where
    evaluate predicate =
        case predicate of
            Predicate.PredicateTrue -> return (Just True)
            Predicate.PredicateFalse -> return (Just False)
            _ -> decidePredicate SideCondition.top (predicate :| [])

instance
    InternalVariable variable =>
    Evaluable (SideCondition variable, Predicate variable)
    where
    evaluate (sideCondition, predicate) =
        case predicate of
            Predicate.PredicateTrue -> return (Just True)
            Predicate.PredicateFalse -> return (Just False)
            _ ->
                decidePredicate sideCondition $
                    predicate :| [from @_ @(Predicate _) sideCondition]

instance InternalVariable variable => Evaluable (Conditional variable term) where
    evaluate conditional =
        assert (Conditional.isNormalized conditional) $
            evaluate (Conditional.predicate conditional)

instance
    InternalVariable variable =>
    Evaluable (SideCondition variable, Conditional variable term)
    where
    evaluate (sideCondition, conditional) =
        assert (Conditional.isNormalized conditional) $
            evaluate (sideCondition, Condition.toPredicate condition)
      where
        condition = Conditional.withoutTerm conditional

-- | Removes all branches refuted by an external SMT solver.
filterBranch ::
    forall simplifier thing.
    MonadSimplify simplifier =>
    Evaluable thing =>
    thing ->
    LogicT simplifier thing
filterBranch thing =
    evaluate thing >>= \case
        Just False -> empty
        _ -> return thing

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
    elements <- mapM refute (toList multiOr)
    return (MultiOr.make (catMaybes elements))
  where
    refute ::
        Conditional variable term ->
        simplifier (Maybe (Conditional variable term))
    refute p = do
        evaluated <- evaluate p
        return $ case evaluated of
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
translateTerm t (UninterpretedTerm pat) = do
    TranslatorState{quantifiedVars, terms} <- State.get
    let freeVars =
            TermLike.freeVariables @_ @variable pat
                & FreeVariables.toNames
        boundVarsMap =
            Map.filterWithKey
                (\k _ -> inject (variableName k) `Set.member` freeVars)
                quantifiedVars
        boundPat = TermLike.mkExistsN (Map.keys boundVarsMap) pat
    lookupUninterpreted boundPat quantifiedVars terms
        <|> declareUninterpreted boundPat boundVarsMap
  where
    lookupUninterpreted boundPat quantifiedVars terms =
        maybe empty (translateSMTDependentAtom quantifiedVars) $
            Map.lookup boundPat terms
    declareUninterpreted boundPat boundVarsMap =
        do
            n <- Counter.increment
            logVariableAssignment n boundPat
            let smtName = "<" <> Text.pack (show n) <> ">"
                (boundVars, bindings) = unzip $ Map.assocs boundVarsMap
                cached = SMTDependentAtom{smtName, smtType = t, boundVars}
            _ <-
                SMT.declareFun
                    SMT.FunctionDeclaration
                        { name = Atom smtName
                        , inputSorts = smtType <$> bindings
                        , resultSort = t
                        }
            field @"terms" Lens.%= Map.insert boundPat cached
            translateSMTDependentAtom boundVarsMap cached

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
    InternalVariable variable =>
    MonadLog m =>
    Counter.Natural ->
    -- | variable to be declared
    TermLike variable ->
    Translator variable m ()
logVariableAssignment n pat =
    logDebug
        . Text.pack
        . show
        . Pretty.nest 4
        . Pretty.sep
        $ [Pretty.pretty n, "|->", unparse pat]
