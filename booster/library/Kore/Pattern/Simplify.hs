{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.Pattern.Simplify (
    simplifyPattern,
    simplifyPredicate,
) where

import Kore.Pattern.Base

simplifyPattern :: Pattern -> Pattern
simplifyPattern = id -- FIXME

simplifyPredicate :: Predicate -> Predicate
simplifyPredicate = id -- FIXME
