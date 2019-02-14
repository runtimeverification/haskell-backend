{-|
Module      : Kore.Step.Condition.Evaluator
Description : Evaluates conditions.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Condition.Evaluator
    ( evaluate
    , refutePredicate
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import           Control.Error
                 ( MaybeT, runMaybeT )
import qualified Control.Monad.Counter as Counter
import qualified Control.Monad.State.Strict as State
import qualified Data.Map.Strict as Map
import           Data.Proxy
import           Data.Reflection
import qualified Data.Text as Text

import           Kore.AST.Pure
import           Kore.Debug
import           Kore.IndexedModule.MetadataTools
import           Kore.Predicate.Predicate
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, PredicateSubstitution, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( isFalse, isTrue, toExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier,
                 SimplificationProof (SimplificationProof), Simplifier,
                 StepPatternSimplifier (..) )
import           Kore.Step.StepperAttributes
import           Kore.Step.TranslateSMT
import           Kore.Unparser
import           SMT
                 ( MonadSMT, Result (..), SExpr (..), SMT )
import qualified SMT

{- | Attempt to evaluate a predicate.

If the predicate is non-trivial (not @\\top{_}()@ or @\\bottom{_}()@),
@evaluate@ attempts to refute the predicate using an external SMT solver.

 -}
evaluate
    ::  forall level variable .
        ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , Given (MetadataTools level StepperAttributes)
        )
    => PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -- ^ Evaluates functions in a pattern.
    -> Predicate level variable
    -- ^ The condition to be evaluated.
    -- TODO: Can't it happen that I also get a substitution when evaluating
    -- functions? See the Equals case.
    -> Simplifier
        (PredicateSubstitution level variable, SimplificationProof level)
evaluate
    substitutionSimplifier
    (StepPatternSimplifier simplifier)
    predicate
  = do
    (simplified, _proof) <-
        simplifier substitutionSimplifier (unwrapPredicate predicate)
    refute <-
        case () of
            _ | OrOfExpandedPattern.isTrue simplified -> return (Just True)
              | OrOfExpandedPattern.isFalse simplified -> return (Just False)
              | otherwise -> refutePredicate predicate
    let simplified' =
            case refute of
                Just False -> ExpandedPattern.bottom
                _ -> OrOfExpandedPattern.toExpandedPattern simplified
        (subst, _proof) = asPredicateSubstitution simplified'
    return (subst, SimplificationProof)

asPredicateSubstitution
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => ExpandedPattern level variable
    -> (PredicateSubstitution level variable, SimplificationProof level)
asPredicateSubstitution
    Predicated {term, predicate, substitution}
  =
    let
        andPatt = makeAndPredicate predicate (wrapPredicate term)
    in
        ( Predicated
            { term = ()
            , predicate = andPatt
            , substitution = substitution
            }
        , SimplificationProof
        )

{- | Attempt to refute a predicate using an external SMT solver.

The predicate is always sent to the external solver, even if it is trivial.

 -}
refutePredicate
    :: forall level variable m.
       ( Given (MetadataTools level StepperAttributes)
       , MetaOrObject level
       , Ord (variable level)
       , Show (variable level)
       , Unparse (variable level)
       , SortedVariable variable
       , MonadSMT m
       )
    => Predicate level variable
    -> m (Maybe Bool)
refutePredicate korePredicate =
    traceNonErrorMonad D_SMT_refutePredicate
        [ debugArg "predicate" korePredicate
        ]
    $ case isMetaOrObject (Proxy :: Proxy level) of
        IsMeta   -> return Nothing
        IsObject ->
            SMT.inNewScope $ runMaybeT $ do
                smtPredicate <- goTranslatePredicate korePredicate
                SMT.assert smtPredicate
                result <- SMT.check
                case result of
                    Unsat -> return False
                    _ -> empty

goTranslatePredicate
    :: forall variable.
        (Ord (variable Object)
        , Given (MetadataTools Object StepperAttributes)
        , Unparse (variable Object)
        )
    => Predicate Object variable
    -> MaybeT SMT SExpr
goTranslatePredicate predicate = do
    let translator =
            translatePredicate
                translateUninterpreted
                predicate
    evalTranslator translator

translateUninterpreted
    :: Ord p
    => SExpr  -- ^ type name
    -> p  -- ^ uninterpreted pattern
    -> Translator p SExpr
translateUninterpreted t pat =
    lookupPattern <|> freeVariable
  where
    lookupPattern = do
        result <- State.gets $ Map.lookup pat
        maybe empty (return . fst) result
    freeVariable = do
        n <- Counter.increment
        var <- SMT.declare ("<" <> Text.pack (show n) <> ">") t
        State.modify' (Map.insert pat (var, t))
        return var
