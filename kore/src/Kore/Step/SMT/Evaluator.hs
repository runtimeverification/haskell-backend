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
    , filterMultiOr
    )
    where

import Control.Applicative
    ( (<|>)
    )
import qualified Control.Applicative as Applicative
import Control.Error
    ( MaybeT
    , runMaybeT
    )
import qualified Control.Exception as Exception
import qualified Control.Monad.State.Strict as State
import qualified Data.Map.Strict as Map
import Data.Maybe
    ( catMaybes
    )
import Data.Reflection
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty

import qualified Control.Monad.Counter as Counter
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
import Kore.Internal.TermLike
    ( TermLike
    )
import Kore.Logger
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import qualified Kore.Profiler.Profile as Profile
    ( smtDecision
    )
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Step.SMT.Translate
    ( Translator
    , evalTranslator
    , translatePredicate
    )
import Kore.Syntax.Variable
    ( SortedVariable
    )
import Kore.TopBottom
    ( TopBottom
    )
import Kore.Unparser
import SMT
    ( Result (..)
    , SExpr (..)
    )
import qualified SMT

{- | Class for things that can be evaluated with an SMT solver,
or which contain things that can be evaluated with an SMT solver.
-}
class Evaluable thing where
    {- | Attempt to evaluate the argument with an external SMT solver.
    -}
    evaluate :: MonadSimplify m => thing -> m (Maybe Bool)

instance
    ( SortedVariable variable
    , Ord variable
    , Show variable
    , Unparse variable
    )
    => Evaluable (Syntax.Predicate variable)
  where
    evaluate predicate =
        case predicate of
            Syntax.Predicate.PredicateTrue -> return (Just True)
            Syntax.Predicate.PredicateFalse -> return (Just False)
            _ -> decidePredicate predicate

instance
    ( SortedVariable variable
    , Ord variable
    , Show variable
    , Unparse variable
    )
    => Evaluable (Conditional variable term)
  where
    evaluate conditional =
        Exception.assert (Conditional.isNormalized conditional)
        $ evaluate (Conditional.predicate conditional)

{- | Removes from a MultiOr all items refuted by an external SMT solver. -}
filterMultiOr
    :: forall simplifier term variable
    .   ( MonadSimplify simplifier
        , Ord term
        , Ord variable
        , Show variable
        , SortedVariable variable
        , TopBottom term
        , Unparse variable
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
        ( Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadSimplify simplifier
        )
    => Syntax.Predicate variable
    -> simplifier (Maybe Bool)
decidePredicate korePredicate =
    withLogScope "decidePredicate" $ SMT.withSolver $ runMaybeT $ do
        tools <- Simplifier.askMetadataTools
        smtPredicate <- goTranslatePredicate tools korePredicate
        result <-
            Profile.smtDecision smtPredicate
            $ SMT.withSolver (SMT.assert smtPredicate >> SMT.check)
        case result of
            Unsat   -> return False
            Sat     -> Applicative.empty
            Unknown -> do
                (logWarning . Text.pack . show . Pretty.vsep)
                    [ "Failed to decide predicate:"
                    , Pretty.indent 4 (unparse korePredicate)
                    ]
                Applicative.empty

goTranslatePredicate
    :: forall variable m.
        ( Ord variable
        , Unparse variable
        , SortedVariable variable
        , MonadSimplify m
        )
    => SmtMetadataTools Attribute.Symbol
    -> Syntax.Predicate variable
    -> MaybeT m SExpr
goTranslatePredicate tools predicate = evalTranslator translator
  where
    translator =
        give tools $ translatePredicate translateUninterpreted predicate

translateUninterpreted
    :: ( Ord p
       , p ~ TermLike variable
       , Unparse variable
       , SortedVariable variable
       )
    => MonadSimplify m
    => SExpr  -- ^ type name
    -> p  -- ^ uninterpreted pattern
    -> Translator m p SExpr
translateUninterpreted t pat =
    lookupPattern <|> freeVariable
  where
    lookupPattern = do
        result <- State.gets $ Map.lookup pat
        maybe Applicative.empty (return . fst) result
    freeVariable = do
        n <- Counter.increment
        var <- SMT.declare ("<" <> Text.pack (show n) <> ">") t
        State.modify' (Map.insert pat (var, t))
        logVariableAssignment n
        return var
    logVariableAssignment n =
        withLogScope "Evaluator"
        . withLogScope "translateUninterpreted"
        . logDebug
        . Text.pack . show
        . Pretty.nest 4 . Pretty.sep
        $ [Pretty.pretty n, "|->", unparse pat]
