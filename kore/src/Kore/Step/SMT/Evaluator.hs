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
    , goTranslatePredicate
    ) where

import Prelude.Kore

import Control.Error
    ( MaybeT
    , hoistMaybe
    , runMaybeT
    )
import qualified Control.Lens as Lens
import qualified Control.Monad.State.Strict as State
import Data.Generics.Product.Fields
import qualified Data.Map.Strict as Map
import Data.Reflection
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty

import Branch
    ( BranchT
    )
import qualified Control.Monad.Counter as Counter
import Kore.Attribute.Pattern.FreeVariables
    ( getFreeVariables
    )
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
import Kore.Internal.TermLike
    ( InternalVariable
    , TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Log.DebugEvaluateCondition
    ( debugEvaluateCondition
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
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )
import Log
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
            _ -> decidePredicate predicate

instance InternalVariable variable => Evaluable (Conditional variable term)
  where
    evaluate conditional =
        assert (Conditional.isNormalized conditional)
        $ evaluate (Conditional.predicate conditional)

{- | Removes all branches refuted by an external SMT solver.
 -}
filterBranch
    :: forall simplifier thing
    .  MonadSimplify simplifier
    => Evaluable thing
    => thing
    -> BranchT simplifier thing
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
    :: forall variable simplifier.
        ( InternalVariable variable
        , MonadSimplify simplifier
        )
    => Predicate variable
    -> simplifier (Maybe Bool)
decidePredicate korePredicate =
    SMT.withSolver $ runMaybeT $ do
        debugEvaluateCondition korePredicate
        tools <- Simplifier.askMetadataTools
        smtPredicate <- goTranslatePredicate tools korePredicate
        result <-
            Profile.smtDecision smtPredicate
            $ SMT.withSolver (SMT.assert smtPredicate >> SMT.check)
        case result of
            Unsat   -> return False
            Sat     -> empty
            Unknown -> do
                (logWarning . Text.pack . show . Pretty.vsep)
                    [ "Failed to decide predicate:"
                    , Pretty.indent 4 (unparse korePredicate)
                    ]
                empty

goTranslatePredicate
    :: forall variable m.
        ( InternalVariable variable
        , SMT.MonadSMT m
        , MonadLog m
        )
    => SmtMetadataTools Attribute.Symbol
    -> Predicate variable
    -> MaybeT m SExpr
goTranslatePredicate tools predicate = evalTranslator translator
  where
    translator =
        give tools $ translatePredicate translateTerm predicate

translateTerm
    :: InternalVariable variable
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
    let freeVars = getFreeVariables $ TermLike.freeVariables pat
        boundVarsMap =
            Map.filterWithKey
                (\k _ -> ElemVar k `Set.member` freeVars)
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
