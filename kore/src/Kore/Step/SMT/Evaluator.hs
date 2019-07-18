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
    )
    where

import           Control.Applicative
                 ( (<|>) )
import qualified Control.Applicative as Applicative
import           Control.Error
                 ( MaybeT, runMaybeT )
import           Control.Monad
                 ( when )
import qualified Control.Monad.State.Strict as State
import qualified Data.Map.Strict as Map
import           Data.Reflection
import qualified Data.Text as Text

import qualified Control.Monad.Counter as Counter
import qualified Kore.Attribute.Symbol as Attribute
                 ( Symbol )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.Conditional
                 ( Conditional )
import qualified Kore.Internal.Conditional as Conditional
import           Kore.Internal.MultiOr
                 ( MultiOr )
import qualified Kore.Internal.MultiOr as MultiOr
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import           Kore.Step.Simplification.Data
                 ( MonadSimplify )
import qualified Kore.Step.Simplification.Data as Simplifier
import           Kore.Step.SMT.Translate
                 ( Translator, evalTranslator, translatePredicate )
import           Kore.Syntax.Variable
                 ( SortedVariable )
import           Kore.TopBottom
                 ( TopBottom )
import           Kore.Unparser
                 ( Unparse, unparseToString )
import           SMT
                 ( Result (..), SExpr (..) )
import qualified SMT

{- | Class for things that can be evaluated with an SMT solver,
or which contain things that can be evaluated with an SMT solver.
-}
class Evaluable thing where
    {- | Attempt to evaluate the argument wiith an external SMT solver.
    -}
    evaluate :: MonadSimplify m => thing -> m thing

instance
    ( SortedVariable variable
    , Ord variable
    , Show variable
    , Unparse variable
    )
    => Evaluable (Syntax.Predicate variable)
  where
    evaluate predicate = do
        refute <- decidePredicate predicate
        return $ case refute of
            Just False -> Syntax.Predicate.makeFalsePredicate
            Just True -> Syntax.Predicate.makeTruePredicate
            Nothing -> predicate

instance
    ( SortedVariable variable
    , Ord variable
    , Show variable
    , Unparse variable
    )
    => Evaluable (Conditional variable term)
  where
    evaluate patt = do
        evaluatedPredicate <- case Predicate.toPredicate predicate of
            Syntax.Predicate.PredicateTrue -> return predicate
            Syntax.Predicate.PredicateFalse -> return predicate
            syntaxPredicate -> do
                evaluatedPredicate <- evaluate syntaxPredicate
                case evaluatedPredicate of
                    Syntax.Predicate.PredicateTrue -> return Predicate.top
                    Syntax.Predicate.PredicateFalse -> return Predicate.bottom
                    _ -> do
                        when (syntaxPredicate /= evaluatedPredicate)
                            ((error . unlines)
                                [ "Unexpected SMT change in syntax predicate:"
                                , "original=" ++ unparseToString syntaxPredicate
                                , "changed="
                                    ++ unparseToString evaluatedPredicate
                                ]
                            )
                        return predicate
        return (term `Conditional.withCondition` evaluatedPredicate)
      where
        (term, predicate) = Conditional.splitTerm patt

instance
    ( SortedVariable variable
    , Ord term
    , Ord variable
    , Show variable
    , TopBottom term
    , Unparse variable
    )
    => Evaluable (MultiOr (Conditional variable term))
  where
    evaluate orPattern = do
        patterns <- mapM evaluate (MultiOr.extractPatterns orPattern)
        return (MultiOr.make patterns)

{- | Attempt to refute a predicate using an external SMT solver.

The predicate is always sent to the external solver, even if it is trivial.
-}
decidePredicate
    :: forall variable m.
        ( Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadSimplify m
        )
    => Syntax.Predicate variable
    -> m (Maybe Bool)
decidePredicate korePredicate =
    SMT.withSolver $ runMaybeT $ do
        tools <- Simplifier.askMetadataTools
        smtPredicate <- goTranslatePredicate tools korePredicate
        result <- SMT.withSolver (SMT.assert smtPredicate >> SMT.check)
        case result of
            Unsat -> return False
            _ -> Applicative.empty

goTranslatePredicate
    :: forall variable m.
        ( Ord variable
        , Unparse variable
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
    :: Ord p
    => SMT.MonadSMT m
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
