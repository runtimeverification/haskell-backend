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
    , evalSimplifier
    , MonadPureMLPatternSimplifier (MonadPureMLPatternSimplifier)
    , PureMLPatternSimplifier
    , SimplificationProof (..)
    , MonadPredicateSimplifier (..)
    , PredicateSimplifier
    ) where

import Kore.AST.Common
       ( SortedVariable )
import Kore.AST.MetaOrObject
import Kore.AST.PureML
       ( PureMLPattern )
import Kore.Predicate.Predicate
       ( Predicate )
import Kore.Step.ExpandedPattern
       ( PredicateSubstitution )
import Kore.Step.OrOfExpandedPattern
       ( OrOfExpandedPattern )
import Kore.Substitution.Class
       ( Hashable )
import Kore.Variables.Fresh

{-| 'SimplificationProof' is a placeholder for proofs showing that the
simplification of a MetaMLPattern was correct.
-}
data SimplificationProof level = SimplificationProof
    deriving (Show, Eq)

type Simplifier = Counter

{-| Run a simplifier computation.

  The result is returned along with the final 'Counter'.

 -}
runSimplifier
    :: Simplifier a
    -- ^ simplifier computation
    -> Natural
    -- ^ initial counter for fresh variables
    -> (a, Natural)
runSimplifier = runCounter

{- | Evaluate a simplifier computation.

  Only the result is returned. The 'IntCounter' is discarded.

  -}
evalSimplifier :: Simplifier a -> a
evalSimplifier simplifier =
    let
        (result, _) = runSimplifier simplifier 0
    in
      result

{-| 'PureMLPatternSimplifier' wraps a function that evaluates
Kore functions on PureMLPatterns.
-}
type PureMLPatternSimplifier level =
    MonadPureMLPatternSimplifier level Simplifier

{-| 'PureMLPatternSimplifier' wraps a function that evaluates
Kore functions on PureMLPatterns.
-}
newtype MonadPureMLPatternSimplifier level m =
    MonadPureMLPatternSimplifier
        (forall variable
        .   ( FreshVariable variable
            , Hashable variable
            , Ord (variable level)
            , Ord (variable Meta)
            , Ord (variable Object)
            , Show (variable level)
            , Show (variable Meta)
            , Show (variable Object)
            , SortedVariable variable
            )
        => PureMLPattern level variable
        -> m
            ( OrOfExpandedPattern level variable
            , SimplificationProof level
            )
        )

type PredicateSimplifier level =
    MonadPredicateSimplifier level Simplifier

newtype MonadPredicateSimplifier level m =
    MonadPredicateSimplifier
        (forall variable
        .   ( FreshVariable variable
            , Hashable variable
            , Ord (variable level)
            , Ord (variable Meta)
            , Ord (variable Object)
            , Show (variable level)
            , Show (variable Meta)
            , Show (variable Object)
            , SortedVariable variable
            )
        => Predicate level variable
        -> m
            ( PredicateSubstitution level variable
            , SimplificationProof level
            )
        )
