module Test.Kore.Rewrite.Rule.Common (
    Pair (..),
    RuleBase (..),
) where

import qualified Data.Default as Default
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    Predicate,
    makeTruePredicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike (
    TermLike,
    VariableName,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Reachability (
    OnePathClaim (..),
    mkOnePathClaim,
 )
import Kore.Rewrite.RewritingVariable (
    mkRuleVariable,
 )
import Kore.Rewrite.RulePattern (
    RHS (RHS),
    RewriteRule (RewriteRule),
    RulePattern (RulePattern),
 )
import qualified Kore.Rewrite.RulePattern as OLD
import Prelude.Kore

newtype Pair variable = Pair (TermLike variable, Predicate variable)

class RuleBase base rule where
    rewritesTo :: base VariableName -> base VariableName -> rule
    rewritesToWithSort :: base VariableName -> base VariableName -> rule

instance RuleBase Pair OnePathClaim where
    Pair (t1, p1) `rewritesTo` Pair (t2, p2) =
        mkOnePathClaim
            (Pattern.fromTermAndPredicate t1' p1')
            (Pattern.fromTermAndPredicate t2' p2' & OrPattern.fromPattern)
            []
      where
        t1' = TermLike.mapVariables (pure mkRuleVariable) t1
        t2' = TermLike.mapVariables (pure mkRuleVariable) t2
        p1' = Predicate.mapVariables (pure mkRuleVariable) p1
        p2' = Predicate.mapVariables (pure mkRuleVariable) p2

    rewritesToWithSort = rewritesTo

instance RuleBase TermLike OnePathClaim where
    t1 `rewritesTo` t2 =
        Pair (t1, makeTruePredicate)
            `rewritesTo` Pair (t2, makeTruePredicate)

    t1 `rewritesToWithSort` t2 =
        Pair (t1, makeTruePredicate)
            `rewritesToWithSort` Pair (t2, makeTruePredicate)

instance RuleBase Pair (RewriteRule VariableName) where
    Pair (t1, p1) `rewritesTo` Pair (t2, p2) =
        RewriteRule
            RulePattern
                { OLD.left = t1
                , OLD.requires = p1
                , OLD.rhs =
                    RHS
                        { OLD.existentials = []
                        , OLD.right = t2
                        , OLD.ensures = p2
                        }
                , OLD.antiLeft = Nothing
                , OLD.attributes = Default.def
                }
    rewritesToWithSort = rewritesTo

instance RuleBase TermLike (RewriteRule VariableName) where
    t1 `rewritesTo` t2 =
        Pair (t1, makeTruePredicate)
            `rewritesTo` Pair (t2, makeTruePredicate)

    t1 `rewritesToWithSort` t2 =
        Pair (t1, makeTruePredicate)
            `rewritesToWithSort` Pair (t2, makeTruePredicate)
