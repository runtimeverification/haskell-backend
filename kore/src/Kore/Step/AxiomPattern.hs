{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Kore.Step.AxiomPattern (
    AxiomPattern (..),
) where

import Kore.Internal.TermLike (
    InternalVariable,
    TermLike,
    VariableName,
 )
import Kore.Step.RulePattern (
    RewriteRule,
    rewriteRuleToTerm,
 )
import Kore.Unparser (
    Unparse (..),
 )
import Prelude.Kore

{- | A wrapper over 'TermLike variable'. It represents a rewrite axiom
 or claim as a Matching Logic pattern.
-}
newtype AxiomPattern variable = AxiomPattern {getAxiomPattern :: TermLike variable}
    deriving stock (Show, Eq)

instance Unparse (AxiomPattern VariableName) where
    unparse = unparse . getAxiomPattern
    unparse2 = unparse2 . getAxiomPattern

instance
    InternalVariable variable =>
    From (RewriteRule variable) (AxiomPattern variable)
    where
    from = AxiomPattern . rewriteRuleToTerm
