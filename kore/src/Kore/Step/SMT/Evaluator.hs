{-|
Module      : Kore.Step.SMT.Evaluator
Description : Uses a SMT solver for evaluating predicates.
Copyright   : (c) Runtime Verification, 2018-2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
-}

module Kore.Step.SMT.Evaluator (decidePredicate) where

import           Control.Applicative
                 ( (<|>) )
import qualified Control.Applicative as Applicative
import           Control.Error
                 ( MaybeT, runMaybeT )
import           Control.Monad.IO.Class
                 ( MonadIO )
import           Control.Monad.Reader
                 ( MonadReader )
import qualified Control.Monad.State.Strict as State
import qualified Data.Map.Strict as Map
import           Data.Reflection
                 ( Given )
import qualified Data.Text as Text

import qualified Control.Monad.Counter as Counter
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Predicate.Predicate
                 ( Predicate )
import           Kore.Step.SMT.Translate
                 ( Translator, evalTranslator, translatePredicate )
import           Kore.Syntax.Variable
                 ( SortedVariable )
import           Kore.Unparser
                 ( Unparse )
import           SMT
                 ( Environment, MonadSMT, Result (..), SExpr (..), SMT )
import qualified SMT



{- | Attempt to refute a predicate using an external SMT solver.

The predicate is always sent to the external solver, even if it is trivial.
-}
decidePredicate
    :: forall variable m.
        ( Given (SmtMetadataTools StepperAttributes)
        , Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadSMT m
        , MonadIO m
        )
    => Predicate variable
    -> m (Maybe Bool)
decidePredicate korePredicate =
    SMT.withSolver $ runMaybeT $ do
        smtPredicate <-
            goTranslatePredicate korePredicate
        -- smtPredicate' <-
        --     goTranslatePredicate (makeNotPredicate korePredicate)
        result <- SMT.withSolver
            (SMT.assert smtPredicate >> SMT.check)
        -- result' <- SMT.inNewScope
        --     (SMT.assert smtPredicate' >> SMT.check)
        -- case (result, result') of
        --     (Unsat, _) -> return False
        --     (_, Unsat) -> return True
        --     _ -> empty
        case result of
            Unsat -> return False
            _ -> Applicative.empty

goTranslatePredicate
    :: forall variable m.
        ( Ord variable
        , Given (SmtMetadataTools StepperAttributes)
        , Unparse variable
        , MonadIO m
        , MonadSMT m
        )
    => Predicate variable
    -> MaybeT m SExpr
goTranslatePredicate predicate = do
    let
        translator = translatePredicate translateUninterpreted predicate
    evalTranslator translator

translateUninterpreted
    :: Ord p
    => MonadIO m
    => MonadSMT m
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
        return var
