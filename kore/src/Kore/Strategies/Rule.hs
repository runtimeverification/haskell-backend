{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}
module Kore.Strategies.Rule
    ( Rule (..)
    -- * Re-exports
    , RewriteRule (..)
    , AllPathRule
    , OnePathRule
    , ReachabilityRule
    ) where

import Prelude.Kore

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Debug
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Label as Attribute
    ( Label
    )
import Kore.Attribute.RuleIndex as Attribute
    ( RuleIndex
    )
import Kore.Attribute.SourceLocation as Attribute
    ( SourceLocation
    )
import Kore.Rewriting.RewritingVariable
import Kore.Step.ClaimPattern
    ( AllPathRule
    , OnePathRule
    , ReachabilityRule
    )
import Kore.Step.RulePattern
    ( RewriteRule (..)
    , ToRulePattern (..)
    , unRewritingRule
    )
import Kore.Unparser
    ( Unparse
    )

{- | @Rule goal@ is the type of rule to take a single step toward @goal@.
 -}
data family Rule goal

-- * One-path reachability

newtype instance Rule OnePathRule =
    OnePathRewriteRule { unRuleOnePath :: RewriteRule RewritingVariableName }
    deriving (GHC.Generic, Show, Unparse)

instance SOP.Generic (Rule OnePathRule)

instance SOP.HasDatatypeInfo (Rule OnePathRule)

instance Debug (Rule OnePathRule)

instance Diff (Rule OnePathRule)

instance ToRulePattern (Rule OnePathRule) where
    toRulePattern = getRewriteRule . unRewritingRule . unRuleOnePath

instance From (Rule OnePathRule) Attribute.PriorityAttributes where
    from = from @(RewriteRule _) . unRuleOnePath

-- * All-path reachability

newtype instance Rule AllPathRule =
    AllPathRewriteRule { unRuleAllPath :: RewriteRule RewritingVariableName }
    deriving (GHC.Generic, Show, Unparse)

instance SOP.Generic (Rule AllPathRule)

instance SOP.HasDatatypeInfo (Rule AllPathRule)

instance Debug (Rule AllPathRule)

instance Diff (Rule AllPathRule)

instance ToRulePattern (Rule AllPathRule) where
    toRulePattern = getRewriteRule . unRewritingRule . unRuleAllPath

instance From (Rule AllPathRule) Attribute.PriorityAttributes where
    from = from @(RewriteRule _) . unRuleAllPath

-- * Reachability

newtype instance Rule ReachabilityRule =
    ReachabilityRewriteRule
        { unReachabilityRewriteRule :: RewriteRule RewritingVariableName }
    deriving (GHC.Generic, Show, Unparse)

instance SOP.Generic (Rule ReachabilityRule)

instance SOP.HasDatatypeInfo (Rule ReachabilityRule)

instance Debug (Rule ReachabilityRule)

instance Diff (Rule ReachabilityRule)

instance ToRulePattern (Rule ReachabilityRule) where
    toRulePattern = getRewriteRule . unRewritingRule . unReachabilityRewriteRule

instance From (Rule ReachabilityRule) Attribute.PriorityAttributes where
    from = from @(RewriteRule _) . unReachabilityRewriteRule

instance From (Rule ReachabilityRule) Attribute.SourceLocation where
    from = from @(RewriteRule _) . unReachabilityRewriteRule

instance From (Rule ReachabilityRule) Attribute.Label where
    from = from @(RewriteRule _) . unReachabilityRewriteRule

instance From (Rule ReachabilityRule) Attribute.RuleIndex where
    from = from @(RewriteRule _) . unReachabilityRewriteRule
