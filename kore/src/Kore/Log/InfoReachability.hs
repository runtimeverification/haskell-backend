{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}
module Kore.Log.InfoReachability
    ( InfoReachability (..)
    , whileSimplify
    , whileCheckImplication
    , whileDeriveSeq
    , whileDerivePar
    ) where

import Prelude.Kore

import Kore.Strategies.Rule
import Log
import qualified Pretty

data InfoReachability
    = InfoSimplify !ReachabilityRule
    | InfoCheckImplication !ReachabilityRule
    | InfoDeriveSeq ![Rule ReachabilityRule] !ReachabilityRule
    | InfoDerivePar ![Rule ReachabilityRule] !ReachabilityRule
    deriving (Show)

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

instance Pretty.Pretty InfoReachability where
    pretty (InfoSimplify goal) =
        prettyInfoReachabilityGoal "Simplify" goal
    pretty (InfoCheckImplication goal) =
        prettyInfoReachabilityGoal "CheckImplication" goal
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

instance Entry InfoReachability where
    entrySeverity _ = Info
    shortDoc (InfoSimplify _) =
        Just "While simplifying the configuration"
    shortDoc (InfoCheckImplication _) =
        Just "While checking implication of the proof goal"
    shortDoc (InfoDeriveSeq _ _) =
        Just "While applying axioms in sequence"
    shortDoc (InfoDerivePar _ _) =
        Just "While applying axioms in parallel"
    helpDoc _ = "log reachability proof steps"

whileSimplify
    :: MonadLog log
    => ReachabilityRule
    -> log a
    -> log a
whileSimplify goal = logWhile (InfoSimplify goal)

whileCheckImplication
    :: MonadLog log
    => ReachabilityRule
    -> log a
    -> log a
whileCheckImplication goal = logWhile (InfoCheckImplication goal)

whileDeriveSeq
    :: MonadLog log
    => [Rule ReachabilityRule]
    -> ReachabilityRule
    -> log a
    -> log a
whileDeriveSeq rules goal = logWhile (InfoDeriveSeq rules goal)

whileDerivePar
    :: MonadLog log
    => [Rule ReachabilityRule]
    -> ReachabilityRule
    -> log a
    -> log a
whileDerivePar rules goal = logWhile (InfoDerivePar rules goal)
