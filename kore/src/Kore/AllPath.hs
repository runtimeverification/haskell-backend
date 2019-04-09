{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.AllPath where

import Data.Maybe
       ( mapMaybe )

import qualified Kore.Step.Representation.MultiOr as MultiOr
import qualified Kore.Step.Strategy as Strategy

data ProofState pattern'
    = GoalLHS pattern'
    | GoalRemLHS pattern'
    | Proven

{- | The final nodes of an execution graph which were not proven.

See also: 'Strategy.pickFinal'

 -}
unprovenNodes
    :: Strategy.ExecutionGraph (ProofState pattern') rule
    -> MultiOr.MultiOr pattern'
unprovenNodes executionGraph =
    MultiOr.MultiOr
    $ mapMaybe getUnprovenNode
    $ Strategy.pickFinal executionGraph
  where
    getUnprovenNode (GoalLHS t)    = Just t
    getUnprovenNode (GoalRemLHS t) = Just t
    getUnprovenNode Proven         = Nothing
