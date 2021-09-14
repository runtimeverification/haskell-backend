{- |
Copyright   : (c) Runtime Verification, 2021
License     : BSD-3-Clause
-}
module Kore.Rewrite.Axiom.MatcherData (
    MatchResult
) where

import qualified Data.Map.Strict as Map
import Kore.Internal.Predicate (Predicate)
import Kore.Internal.TermLike (TermLike, SomeVariableName)

type MatchResult variable =
    ( Predicate variable
    , Map.Map (SomeVariableName variable) (TermLike variable)
    )

