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

-- * Reachability

newtype instance Rule (ReachabilityRule Variable) =
    ReachabilityRewriteRule
        { unReachabilityRewriteRule :: RewriteRule Variable }
    deriving (GHC.Generic, Show, Unparse)

instance SOP.Generic (Rule (ReachabilityRule Variable))

instance SOP.HasDatatypeInfo (Rule (ReachabilityRule Variable))

instance Debug (Rule (ReachabilityRule Variable))

instance Diff (Rule (ReachabilityRule Variable))

instance ToRulePattern (Rule (ReachabilityRule Variable))

instance FromRulePattern (Rule (ReachabilityRule Variable))
