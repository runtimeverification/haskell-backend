{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}
module Kore.Log.InfoReachability
    ( InfoReachability (..)
    , whileSimplify
    , whileRemoveDestination
    , whileDeriveSeq
    , whileDerivePar
    , prettyInfoReachabilityGoal
    , prettyInfoReachabilityGoalAndRules
    ) where

-- TODO: Do not export prettyInfoReachabilityGoal.
-- TODO: Do not export prettyInfoReachabilityGoalAndRules.

import Prelude.Kore

import Kore.Internal.Variable
    ( Variable
    )
import Kore.Strategies.Rule
import Log
import qualified Pretty

data InfoReachability goal
    = InfoSimplify !goal
    | InfoRemoveDestination !goal
    | InfoDeriveSeq ![Rule goal] !goal
    | InfoDerivePar ![Rule goal] !goal

prettyInfoReachabilityGoal
    :: Pretty.Pretty goal
    => Pretty.Doc ann
    -> goal
    -> Pretty.Doc ann
prettyInfoReachabilityGoal transition goal =
    Pretty.vsep
        [ "transition:"
        , transition
        , "goal:"
        , Pretty.pretty goal
        ]

prettyInfoReachabilityGoalAndRules
    :: Pretty.Pretty goal
    => Pretty.Pretty rule
    => Pretty.Doc ann
    -> goal
    -> [Rule goal]
    -> (Rule goal -> rule)
    -> Pretty.Doc ann
prettyInfoReachabilityGoalAndRules transition goal rules fromRule =
    Pretty.vsep
        [ prettyInfoReachabilityGoal transition goal
        , "rules:"
        , Pretty.pretty $ fmap fromRule rules
        ]

instance Pretty.Pretty (InfoReachability (ReachabilityRule Variable)) where
    pretty (InfoSimplify goal) =
        prettyInfoReachabilityGoal "Simplify" goal
    pretty (InfoRemoveDestination goal) =
        prettyInfoReachabilityGoal "RemoveDestination" goal
    pretty (InfoDeriveSeq rules goal) =
        prettyInfoReachabilityGoalAndRules
            "DeriveSeq"
            goal
            rules
            (getRewriteRule . unReachabilityRewriteRule)
    pretty (InfoDerivePar rules goal) =
        prettyInfoReachabilityGoalAndRules
            "DerivePar"
            goal
            rules
            (getRewriteRule . unReachabilityRewriteRule)

instance Pretty.Pretty (InfoReachability (OnePathRule Variable)) where
    pretty (InfoSimplify rule) =
        prettyInfoReachabilityGoal "Simplify" rule
    pretty (InfoRemoveDestination rule) =
        prettyInfoReachabilityGoal "RemoveDestination" rule
    pretty (InfoDeriveSeq rules goal) =
        prettyInfoReachabilityGoalAndRules
            "DeriveSeq"
            goal
            rules
            (getRewriteRule . unRuleOnePath)
    pretty (InfoDerivePar rules goal) =
        prettyInfoReachabilityGoalAndRules
            "DerivePar"
            goal
            rules
            (getRewriteRule . unRuleOnePath)

instance Pretty.Pretty (InfoReachability (AllPathRule Variable)) where
    pretty (InfoSimplify rule) =
        prettyInfoReachabilityGoal "Simplify" rule
    pretty (InfoRemoveDestination rule) =
        prettyInfoReachabilityGoal "RemoveDestination" rule
    pretty (InfoDeriveSeq rules goal) =
        prettyInfoReachabilityGoalAndRules
            "DeriveSeq"
            goal
            rules
            (getRewriteRule . unRuleAllPath)
    pretty (InfoDerivePar rules goal) =
        prettyInfoReachabilityGoalAndRules
            "DerivePar"
            goal
            rules
            (getRewriteRule . unRuleAllPath)

instance Entry (InfoReachability (ReachabilityRule Variable)) where
    entrySeverity _ = Info

instance Entry (InfoReachability (OnePathRule Variable)) where
    entrySeverity _ = Info

instance Entry (InfoReachability (AllPathRule Variable)) where
    entrySeverity _ = Info

whileSimplify
    :: MonadLog log
    => Entry (InfoReachability goal)
    => goal
    -> log a
    -> log a
whileSimplify goal = logWhile (InfoSimplify goal)

whileRemoveDestination
    :: MonadLog log
    => Entry (InfoReachability goal)
    => goal
    -> log a
    -> log a
whileRemoveDestination goal = logWhile (InfoRemoveDestination goal)

whileDeriveSeq
    :: MonadLog log
    => Entry (InfoReachability goal)
    => [Rule goal]
    -> goal
    -> log a
    -> log a
whileDeriveSeq rules goal = logWhile (InfoDeriveSeq rules goal)

whileDerivePar
    :: MonadLog log
    => Entry (InfoReachability goal)
    => [Rule goal]
    -> goal
    -> log a
    -> log a
whileDerivePar rules goal = logWhile (InfoDerivePar rules goal)
