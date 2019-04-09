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

{- | Extract the unproven part of a 'ProofState'.

Returns 'Nothing' if there is no remaining unproven part.

 -}
extractUnproven :: ProofState pattern' -> Maybe pattern'
extractUnproven (GoalLHS t)    = Just t
extractUnproven (GoalRemLHS t) = Just t
extractUnproven Proven         = Nothing

{- | The final nodes of an execution graph which were not proven.

See also: 'Strategy.pickFinal', 'extractUnproven'

 -}
unprovenNodes
    :: Strategy.ExecutionGraph (ProofState pattern') rule
    -> MultiOr.MultiOr pattern'
unprovenNodes executionGraph =
    MultiOr.MultiOr
    $ mapMaybe extractUnproven
    $ Strategy.pickFinal executionGraph
