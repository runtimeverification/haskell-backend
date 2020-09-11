{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}
module Kore.Strategies.Rule
    ( Rule (..)
    -- * Re-exports
    , RewriteRule (..)
    , AllPathClaim
    , OnePathClaim
    , ReachabilityClaim
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
    ( AllPathClaim
    , OnePathClaim
    , ReachabilityClaim
    )
import Kore.Step.RulePattern
    ( RewriteRule (..)
    )
import Kore.Unparser
    ( Unparse
    )

{- | @Rule goal@ is the type of rule to take a single step toward @goal@.
 -}
data family Rule goal

-- * One-path reachability

newtype instance Rule OnePathClaim =
    OnePathRewriteRule { unRuleOnePath :: RewriteRule RewritingVariableName }
    deriving (GHC.Generic, Show, Unparse)

instance SOP.Generic (Rule OnePathClaim)

instance SOP.HasDatatypeInfo (Rule OnePathClaim)

instance Debug (Rule OnePathClaim)

instance Diff (Rule OnePathClaim)

instance From (Rule OnePathClaim) Attribute.PriorityAttributes where
    from = from @(RewriteRule _) . unRuleOnePath

-- * All-path reachability

newtype instance Rule AllPathClaim =
    AllPathRewriteRule { unRuleAllPath :: RewriteRule RewritingVariableName }
    deriving (GHC.Generic, Show, Unparse)

instance SOP.Generic (Rule AllPathClaim)

instance SOP.HasDatatypeInfo (Rule AllPathClaim)

instance Debug (Rule AllPathClaim)

instance Diff (Rule AllPathClaim)

instance From (Rule AllPathClaim) Attribute.PriorityAttributes where
    from = from @(RewriteRule _) . unRuleAllPath

-- * Reachability

newtype instance Rule ReachabilityClaim =
    ReachabilityRewriteRule
        { unReachabilityRewriteRule :: RewriteRule RewritingVariableName }
    deriving (GHC.Generic, Show, Unparse)

instance SOP.Generic (Rule ReachabilityClaim)

instance SOP.HasDatatypeInfo (Rule ReachabilityClaim)

instance Debug (Rule ReachabilityClaim)

instance Diff (Rule ReachabilityClaim)

instance From (Rule ReachabilityClaim) Attribute.PriorityAttributes where
    from = from @(RewriteRule _) . unReachabilityRewriteRule

instance From (Rule ReachabilityClaim) Attribute.SourceLocation where
    from = from @(RewriteRule _) . unReachabilityRewriteRule

instance From (Rule ReachabilityClaim) Attribute.Label where
    from = from @(RewriteRule _) . unReachabilityRewriteRule

instance From (Rule ReachabilityClaim) Attribute.RuleIndex where
    from = from @(RewriteRule _) . unReachabilityRewriteRule
