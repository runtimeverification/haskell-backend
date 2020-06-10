{-|
Module      : Kore.Step.SMT.Evaluator
Description : Uses a SMT solver for evaluating predicates.
Copyright   : (c) Runtime Verification, 2018-2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
-}

module Kore.Step.SMT.Evaluator
    ( decidePredicate
    , Evaluable (..)
    , filterBranch
    , filterMultiOr
    , translateTerm
    , translatePredicate
    ) where

import Prelude.Kore

import Control.Error
    ( hoistMaybe
    , runMaybeT
    )
import qualified Control.Lens as Lens
import qualified Control.Monad.State.Strict as State
import qualified Data.Foldable as Foldable
import Data.Generics.Product.Fields
import Data.List.NonEmpty
    ( NonEmpty (..)
    )
import qualified Data.Map.Strict as Map
import Data.Reflection
import qualified Data.Set as Set
import qualified Data.Text as Text

import qualified Control.Monad.Counter as Counter
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import qualified Kore.Attribute.Symbol as Attribute
    ( Symbol
    )
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import Kore.Internal.Conditional
    ( Conditional
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.MultiOr
    ( MultiOr
    )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition
    ( SideCondition
    )
import Kore.Internal.TermLike
    ( InternalVariable
    , TermLike
    , Variable (..)
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Log.DebugEvaluateCondition
    ( debugEvaluateConditionResult
    , whileDebugEvaluateCondition
    )
import Kore.Log.WarnDecidePredicateUnknown
    ( warnDecidePredicateUnknown
    )
import qualified Kore.Profiler.Profile as Profile
    ( smtDecision
    )
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Step.SMT.Translate
import Kore.TopBottom
    ( TopBottom
    )
import Kore.Unparser
import Log
import Logic
    ( LogicT
    )
import qualified Pretty
import SMT
    ( Result (..)
    , SExpr (..)
    )
import qualified SMT
import qualified SMT.SimpleSMT as SimpleSMT

{- | Class for things that can be evaluated with an SMT solver,
or which contain things that can be evaluated with an SMT solver.
-}
class Evaluable thing where
    {- | Attempt to evaluate the argument with an external SMT solver.
    -}
    evaluate :: MonadSimplify m => thing -> m (Maybe Bool)

instance InternalVariable variable => Evaluable (Predicate variable) where
    evaluate predicate =
        case predicate of
            Predicate.PredicateTrue -> return (Just True)
            Predicate.PredicateFalse -> return (Just False)
            _ -> decidePredicate (predicate :| [])

instance
    InternalVariable variable
    => Evaluable (SideCondition variable, Predicate variable)
  where
    evaluate (sideCondition, predicate) =
        case predicate of
            Predicate.PredicateTrue -> return (Just True)
            Predicate.PredicateFalse -> return (Just False)
            _ ->
                decidePredicate
                $ predicate :| [from @_ @(Predicate _) sideCondition]

instance InternalVariable variable => Evaluable (Conditional variable term)
  where
    evaluate conditional =
        assert (Conditional.isNormalized conditional)
        $ evaluate (Conditional.predicate conditional)

instance
    InternalVariable variable
    => Evaluable (SideCondition variable, Conditional variable term)
  where
    evaluate (sideCondition, conditional) =
        assert (Conditional.isNormalized conditional)
        $ evaluate (sideCondition, Conditional.predicate conditional)

{- | Removes all branches refuted by an external SMT solver.
 -}
filterBranch
    :: forall simplifier thing
    .  MonadSimplify simplifier
    => Evaluable thing
    => thing
    -> LogicT simplifier thing
filterBranch thing =
    evaluate thing >>= \case
        Just False -> empty
        _          -> return thing

{- | Removes from a MultiOr all items refuted by an external SMT solver. -}
filterMultiOr
    :: forall simplifier term variable
    .   ( MonadSimplify simplifier
        , Ord term
        , TopBottom term
        , InternalVariable variable
        )
    => MultiOr (Conditional variable term)
    -> simplifier (MultiOr (Conditional variable term))
filterMultiOr multiOr = do
    elements <- mapM refute (MultiOr.extractPatterns multiOr)
    return (MultiOr.make (catMaybes elements))
  where
    refute
        :: Conditional variable term
        -> simplifier (Maybe (Conditional variable term))
    refute p = do
        evaluated <- evaluate p
        return $ case evaluated of
            Nothing -> Just p
            Just False -> Nothing
            Just True -> Just p

{- | Attempt to refute a predicate using an external SMT solver.

The predicate is always sent to the external solver, even if it is trivial.
-}
decidePredicate
    :: forall variable simplifier
    .  InternalVariable variable
    => MonadSimplify simplifier
    => NonEmpty (Predicate variable)
    -> simplifier (Maybe Bool)
decidePredicate predicates =
    whileDebugEvaluateCondition predicates
    $ SMT.withSolver $ runMaybeT $ evalTranslator $ do
        tools <- Simplifier.askMetadataTools
        predicates' <- traverse (translatePredicate tools) predicates
        result <- Profile.smtDecision predicates' $ SMT.withSolver $ do
            Foldable.traverse_ SMT.assert predicates'
            SMT.check
        debugEvaluateConditionResult result
        case result of
            Unsat -> return False
            Sat -> empty
            Unknown -> do
                warnDecidePredicateUnknown predicates
                empty

translatePredicate
    :: forall variable m.
        ( InternalVariable variable
        , SMT.MonadSMT m
        , MonadLog m
        )
    => SmtMetadataTools Attribute.Symbol
    -> Predicate variable
    -> Translator m variable SExpr
translatePredicate tools predicate =
    give tools $ translatePredicateWith translateTerm predicate

translateTerm
    :: forall m variable
    .  InternalVariable variable
    => SMT.MonadSMT m
    => MonadLog m
    => SExpr  -- ^ type name
    -> TranslateItem variable  -- ^ uninterpreted pattern
    -> Translator m variable SExpr
translateTerm smtType (QuantifiedVariable var) = do
    n <- Counter.increment
    let varName = "<" <> Text.pack (show n) <> ">"
        smtVar = SimpleSMT.const varName
    field @"quantifiedVars" Lens.%=
        Map.insert var
            SMTDependentAtom
            { smtName = varName
            , smtType
            , boundVars = []
            }
    return smtVar
translateTerm t (UninterpretedTerm (TermLike.ElemVar_ var)) =
    lookupVariable var <|> declareVariable t var
translateTerm t (UninterpretedTerm pat) = do
    TranslatorState { quantifiedVars, terms } <- State.get
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
        maybe empty (translateSMTDependentAtom quantifiedVars)
        $ Map.lookup boundPat terms
    declareUninterpreted boundPat boundVarsMap
      = do
        n <- Counter.increment
        logVariableAssignment n boundPat
        let smtName = "<" <> Text.pack (show n) <> ">"
            (boundVars, bindings) = unzip $ Map.assocs boundVarsMap
            cached = SMTDependentAtom { smtName, smtType = t, boundVars }
        _ <- SMT.declareFun
            SMT.FunctionDeclaration
                { name = Atom smtName
                , inputSorts = smtType <$> bindings
                , resultSort = t
                }
        field @"terms" Lens.%= Map.insert boundPat cached
        translateSMTDependentAtom boundVarsMap cached

lookupVariable
    :: InternalVariable variable
    => Monad m
    => TermLike.ElementVariable variable
    -> Translator m variable SExpr
lookupVariable var =
    lookupQuantifiedVariable <|> lookupFreeVariable
  where
    lookupQuantifiedVariable = do
        TranslatorState { quantifiedVars } <- State.get
        hoistMaybe $ SMT.Atom . smtName <$> Map.lookup var quantifiedVars
    lookupFreeVariable = do
        TranslatorState { freeVars} <- State.get
        hoistMaybe $ Map.lookup var freeVars

declareVariable
    :: InternalVariable variable
    => SMT.MonadSMT m
    => MonadLog m
    => SExpr  -- ^ type name
    -> TermLike.ElementVariable variable  -- ^ variable to be declared
    -> Translator m variable SExpr
declareVariable t variable = do
    n <- Counter.increment
    let varName = "<" <> Text.pack (show n) <> ">"
    var <- SMT.declare varName t
    field @"freeVars" Lens.%= Map.insert variable var
    logVariableAssignment n (TermLike.mkElemVar variable)
    return var

logVariableAssignment
    :: InternalVariable variable
    => MonadLog m
    => Counter.Natural
    -> TermLike variable  -- ^ variable to be declared
    -> Translator m variable ()
logVariableAssignment n pat =
    logDebug
    . Text.pack . show
    . Pretty.nest 4 . Pretty.sep
    $ [Pretty.pretty n, "|->", unparse pat]
