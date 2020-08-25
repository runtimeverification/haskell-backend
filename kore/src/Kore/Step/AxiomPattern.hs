{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Step.AxiomPattern
    ( AxiomPattern (..)
    ) where

import Prelude.Kore

import Kore.Internal.TermLike
    ( InternalVariable
    , TermLike
    , VariableName
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    , mkRuleVariable
    )
import Kore.Step.ClaimPattern
    ( AllPathRule
    , OnePathRule
    , ReachabilityRule (..)
    , allPathRuleToTerm
    , onePathRuleToTerm
    )
import Kore.Step.RulePattern
    ( RewriteRule
    , rewriteRuleToTerm
    )
import Kore.Unparser
    ( Unparse (..)
    )

-- | A wrapper over 'TermLike variable'. It represents a rewrite axiom
-- or claim as a Matching Logic pattern.
newtype AxiomPattern variable =
    AxiomPattern { getAxiomPattern :: TermLike variable }
    deriving (Show, Eq)

instance Unparse (AxiomPattern VariableName) where
    unparse = unparse . getAxiomPattern
    unparse2 = unparse2 . getAxiomPattern

instance From OnePathRule (AxiomPattern VariableName) where
    from = AxiomPattern . onePathRuleToTerm

instance From OnePathRule (AxiomPattern RewritingVariableName) where
    from =
        AxiomPattern
        . TermLike.mapVariables (pure mkRuleVariable)
        . onePathRuleToTerm

instance From AllPathRule (AxiomPattern VariableName) where
    from = AxiomPattern . allPathRuleToTerm

instance From AllPathRule (AxiomPattern RewritingVariableName) where
    from =
        AxiomPattern
        . TermLike.mapVariables (pure mkRuleVariable)
        . allPathRuleToTerm

instance From ReachabilityRule (AxiomPattern VariableName) where
    from (OnePath rule) = from rule
    from (AllPath rule) = from rule

instance InternalVariable variable =>
    From (RewriteRule variable) (AxiomPattern variable)
  where
    from = AxiomPattern . rewriteRuleToTerm
