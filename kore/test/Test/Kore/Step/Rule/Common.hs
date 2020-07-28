module Test.Kore.Step.Rule.Common
    ( Pair (..)
    , rewritesToOLD
    , rewritesTo
    ) where

import Prelude.Kore


import qualified Data.Default as Default

import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    , makeTruePredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
    ( TermLike
    , VariableName
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewriting.RewritingVariable
    ( mkRuleVariable
    )
import Kore.Step.ClaimPattern
    ( OnePathRule (..)
    , claimPatternInternal
    )
import Kore.Step.RulePattern
    ( RHS (RHS)
    , RulePattern (RulePattern)
    )
import qualified Kore.Step.RulePattern as OLD

newtype Pair variable = Pair (TermLike variable, Predicate variable)

class OnePathRuleBaseOLD base where
    rewritesToOLD :: base VariableName -> base VariableName -> OLD.OnePathRule

instance OnePathRuleBaseOLD Pair where
    Pair (t1, p1) `rewritesToOLD` Pair (t2, p2) =
        OLD.OnePathRule RulePattern
            { OLD.left = t1
            , OLD.requires = p1
            , OLD.rhs = RHS
                { OLD.existentials = []
                , OLD.right = t2
                , OLD.ensures = p2
                }
            , OLD.antiLeft = Nothing
            , OLD.attributes = Default.def
            }

instance OnePathRuleBaseOLD TermLike where
    t1 `rewritesToOLD` t2 =
        Pair (t1, makeTruePredicate (TermLike.termLikeSort t1))
        `rewritesToOLD` Pair (t2, makeTruePredicate (TermLike.termLikeSort t2))

class OnePathRuleBase base where
    rewritesTo :: base VariableName -> base VariableName -> OnePathRule

instance OnePathRuleBase Pair where
    Pair (t1, p1) `rewritesTo` Pair (t2, p2) =
        OnePathRule
        $ claimPatternInternal
            (Pattern.fromTermAndPredicate t1' p1')
            (Pattern.fromTermAndPredicate t2' p2' & OrPattern.fromPattern)
            []
      where
        t1' = TermLike.mapVariables (pure mkRuleVariable) t1
        t2' = TermLike.mapVariables (pure mkRuleVariable) t2
        p1' = Predicate.mapVariables (pure mkRuleVariable) p1
        p2' = Predicate.mapVariables (pure mkRuleVariable) p2

instance OnePathRuleBase TermLike where
    t1 `rewritesTo` t2 =
        Pair (t1, makeTruePredicate (TermLike.termLikeSort t1))
        `rewritesTo` Pair (t2, makeTruePredicate (TermLike.termLikeSort t2))

