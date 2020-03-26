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
    ) where

import Prelude.Kore

import Kore.Internal.Variable
    ( Variable
    )
import Kore.Strategies.Rule
import Log
import qualified Pretty

data InfoReachability
    = InfoSimplify !(ReachabilityRule Variable)
    | InfoRemoveDestination !(ReachabilityRule Variable)
    | InfoDeriveSeq
        ![Rule (ReachabilityRule Variable)]
        !(ReachabilityRule Variable)
    | InfoDerivePar
        ![Rule (ReachabilityRule Variable)]
        !(ReachabilityRule Variable)

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

instance Entry InfoReachability where
    entrySeverity _ = Info
    shortDoc (InfoSimplify _) =
        Just "While simplifying the configuration"
    shortDoc (InfoRemoveDestination _) =
        Just "While removing the destination of the configuration"
    shortDoc (InfoDeriveSeq _ _) =
        Just "While deriving the rules in sequence"
    shortDoc (InfoDerivePar _ _) =
        Just "While deriving the rules in parallel"

whileSimplify
    :: MonadLog log
    => ReachabilityRule Variable
    -> log a
    -> log a
whileSimplify goal = logWhile (InfoSimplify goal)

whileRemoveDestination
    :: MonadLog log
    => ReachabilityRule Variable
    -> log a
    -> log a
whileRemoveDestination goal = logWhile (InfoRemoveDestination goal)

whileDeriveSeq
    :: MonadLog log
    => [Rule (ReachabilityRule Variable)]
    -> ReachabilityRule Variable
    -> log a
    -> log a
whileDeriveSeq rules goal = logWhile (InfoDeriveSeq rules goal)

whileDerivePar
    :: MonadLog log
    => [Rule (ReachabilityRule Variable)]
    -> ReachabilityRule Variable
    -> log a
    -> log a
whileDerivePar rules goal = logWhile (InfoDerivePar rules goal)
