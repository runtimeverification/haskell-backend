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
    , PureMLPatternSimplifier (..)
    , CommonPureMLPatternSimplifier
    , SimplificationProof (..)
      -- * Re-exports
    , Typeable
    ) where

import           Control.Monad.Catch.Pure
                 ( Catch, SomeException )
import qualified Control.Monad.Catch.Pure as Monad.Catch
import           Control.Monad.Reader
import           Data.Typeable
                 ( Typeable )

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

type Simplifier = ReaderT SMTTimeOut (CounterT Catch)

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
    -> Either SomeException (a, Natural)
runSimplifier smtTimeOut simplifier counter =
    Monad.Catch.runCatch
    $ runCounterT (runReaderT simplifier smtTimeOut) counter

{- | Evaluate a simplifier computation.

  Only the result is returned. The 'IntCounter' is discarded.

  -}
evalSimplifierWithTimeout :: SMTTimeOut -> Simplifier a -> Either SomeException a
evalSimplifierWithTimeout smtTimeOut simplifier =
    fst <$> runSimplifier smtTimeOut simplifier 0

evalSimplifier :: Simplifier a -> Either SomeException a
evalSimplifier simplifier =
    evalSimplifierWithTimeout defaultSMTTimeOut simplifier

defaultSMTTimeOut :: SMTTimeOut -- in ms
defaultSMTTimeOut = SMTTimeOut 40

{-| 'PureMLPatternSimplifier' wraps a function that evaluates
Kore functions on PureMLPatterns.
-}
newtype PureMLPatternSimplifier level variable =
    PureMLPatternSimplifier
        ( PredicateSubstitutionSimplifier level
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
newtype PredicateSubstitutionSimplifier level =
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
            , Typeable variable
            )
        => PredicateSubstitution level variable
        -> Simplifier
            ( PredicateSubstitution level variable
            , SimplificationProof level
            )
        )
