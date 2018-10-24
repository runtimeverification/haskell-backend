{-|
Module      : Kore.Step.Simplification.Data
Description : Data structures used for term simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Data
    ( Simplifier
    , runSimplifier
    , evalSimplifierWithTimeout
    , evalSimplifier
    , defaultSMTTimeOut
    , PredicateSubstitutionSimplifier (..)
    , liftPredicateSubstitutionSimplifier
    , PureMLPatternSimplifier (..)
    , CommonPureMLPatternSimplifier
    , SimplificationProof (..)
    ) where

import           Control.Monad.Reader
import qualified Control.Monad.Trans as Monad.Trans

import Kore.AST.Common
       ( PureMLPattern, SortedVariable, Variable )
import Kore.AST.MetaOrObject
       ( Meta, MetaOrObject, Object )
import Kore.SMT.Config
import Kore.Step.OrOfExpandedPattern
       ( OrOfExpandedPattern )
import Kore.Step.PredicateSubstitution
       ( PredicateSubstitution )
import Kore.Substitution.Class
       ( Hashable )
import Kore.Variables.Fresh
{-| 'SimplificationProof' is a placeholder for proofs showing that the
simplification of a MetaMLPattern was correct.
-}
data SimplificationProof level = SimplificationProof
    deriving (Show, Eq)

type Simplifier = ReaderT SMTTimeOut Counter

{- | Run a simplifier computation.

  The result is returned along with the final 'Counter'.

 -}
runSimplifier
    :: SMTTimeOut
    -- ^ Timeout (in ms) for SMT solver
    -> Simplifier a
    -- ^ simplifier computation
    -> Natural
    -- ^ initial counter for fresh variables
    -> (a, Natural)
runSimplifier smtTimeOut = runCounter . flip runReaderT smtTimeOut

{- | Evaluate a simplifier computation.

  Only the result is returned. The 'IntCounter' is discarded.

  -}
evalSimplifierWithTimeout :: SMTTimeOut -> Simplifier a -> a
evalSimplifierWithTimeout smtTimeOut simplifier =
    let
        (result, _) = runSimplifier smtTimeOut simplifier 0
    in
      result

evalSimplifier :: Simplifier a -> a
evalSimplifier simplifier =
    evalSimplifierWithTimeout defaultSMTTimeOut simplifier

defaultSMTTimeOut :: SMTTimeOut -- in ms
defaultSMTTimeOut = SMTTimeOut 40

{-| 'PureMLPatternSimplifier' wraps a function that evaluates
Kore functions on PureMLPatterns.
-}
newtype PureMLPatternSimplifier level variable =
    PureMLPatternSimplifier
        ( PredicateSubstitutionSimplifier level Simplifier
        -> PureMLPattern level variable
        -> Simplifier
            ( OrOfExpandedPattern level variable
            , SimplificationProof level
            )
        )

{-| 'CommonPurePatternFunctionEvaluator' wraps a function that evaluates
Kore functions on CommonPurePatterns.
-}
type CommonPureMLPatternSimplifier level =
    PureMLPatternSimplifier level Variable


{-| 'PredicateSubstitutionSimplifier' wraps a function that simplifies
'PredicateSubstitution's. The minimal requirement from this function is
that it applies the substitution on the predicate.
-}
newtype PredicateSubstitutionSimplifier level m =
    PredicateSubstitutionSimplifier
        (forall variable
        .   ( FreshVariable variable
            , Hashable variable
            , MetaOrObject level
            , Ord (variable level)
            , Ord (variable Meta)
            , Ord (variable Object)
            , Show (variable level)
            , Show (variable Meta)
            , Show (variable Object)
            , SortedVariable variable
            )
        => PredicateSubstitution level variable
        -> m
            ( PredicateSubstitution level variable
            , SimplificationProof level
            )
        )

liftPredicateSubstitutionSimplifier
    :: (MonadTrans t, Monad m)
    => PredicateSubstitutionSimplifier level m
    -> PredicateSubstitutionSimplifier level (t m)
liftPredicateSubstitutionSimplifier
    (PredicateSubstitutionSimplifier simplifier)
  =
    PredicateSubstitutionSimplifier (Monad.Trans.lift . simplifier)
