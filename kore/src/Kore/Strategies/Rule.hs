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
import Kore.Attribute.Label as Attribute
    ( Label
    )
import Kore.Attribute.RuleIndex as Attribute
    ( RuleIndex
    )
import Kore.Attribute.SourceLocation as Attribute
    ( SourceLocation
    )
import Kore.HasPriority
import Kore.Internal.Variable
    ( Variable
    )
import Kore.Step.RulePattern
    ( AllPathRule
    , FromRulePattern
    , OnePathRule
    , ReachabilityRule
    , RewriteRule (..)
    , ToRulePattern
    )
import Kore.Unparser
    ( Unparse
    )

{- | @Rule goal@ is the type of rule to take a single step toward @goal@.
 -}
data family Rule goal

-- * One-path reachability

newtype instance Rule (OnePathRule Variable) =
    OnePathRewriteRule { unRuleOnePath :: RewriteRule Variable }
    deriving (GHC.Generic, Show, Unparse)

instance SOP.Generic (Rule (OnePathRule Variable))

instance SOP.HasDatatypeInfo (Rule (OnePathRule Variable))

instance Debug (Rule (OnePathRule Variable))

instance Diff (Rule (OnePathRule Variable))

instance ToRulePattern (Rule (OnePathRule Variable))

instance FromRulePattern (Rule (OnePathRule Variable))

instance HasPriority (Rule (OnePathRule Variable)) where
    getPriority = getPriority . unRuleOnePath

-- * All-path reachability

newtype instance Rule (AllPathRule Variable) =
    AllPathRewriteRule { unRuleAllPath :: RewriteRule Variable }
    deriving (GHC.Generic, Show, Unparse)

instance SOP.Generic (Rule (AllPathRule Variable))

instance SOP.HasDatatypeInfo (Rule (AllPathRule Variable))

instance Debug (Rule (AllPathRule Variable))

instance Diff (Rule (AllPathRule Variable))

instance ToRulePattern (Rule (AllPathRule Variable))

instance FromRulePattern (Rule (AllPathRule Variable))

instance HasPriority (Rule (AllPathRule Variable)) where
    getPriority = getPriority . unRuleAllPath

-- * Reachability

newtype instance Rule ReachabilityRule =
    ReachabilityRewriteRule
        { unReachabilityRewriteRule :: RewriteRule Variable }
    deriving (GHC.Generic, Show, Unparse)

instance SOP.Generic (Rule ReachabilityRule)

instance SOP.HasDatatypeInfo (Rule ReachabilityRule)

instance Debug (Rule ReachabilityRule)

instance Diff (Rule ReachabilityRule)

instance ToRulePattern (Rule ReachabilityRule)

instance FromRulePattern (Rule ReachabilityRule)

instance HasPriority (Rule ReachabilityRule) where
    getPriority = getPriority . unReachabilityRewriteRule

instance From (Rule ReachabilityRule) Attribute.SourceLocation where
    from = from @(RewriteRule Variable) . unReachabilityRewriteRule

instance From (Rule ReachabilityRule) Attribute.Label where
    from = from @(RewriteRule Variable) . unReachabilityRewriteRule

instance From (Rule ReachabilityRule) Attribute.RuleIndex where
    from = from @(RewriteRule Variable) . unReachabilityRewriteRule
