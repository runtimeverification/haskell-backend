{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Kore.Reachability (
    AllPathClaim (..),
    mkAllPathClaim,
    allPathRuleToTerm,
    OnePathClaim (..),
    mkOnePathClaim,
    onePathRuleToTerm,
    SomeClaim (..),
    mkSomeClaimAllPath,
    mkSomeClaimOnePath,
    makeTrusted,
    lensClaimPattern,
    getConfiguration,
    getDestination,
    AppliedRule (..),
    Rule (..),
    module Kore.Claim.Claim,
    module Kore.Reachability.ClaimState,
    module Kore.Reachability.Prove,
) where

import Kore.Claim.Claim
import Kore.Claim.SomeClaim
import Kore.Reachability.AllPathClaim
import Kore.Reachability.ClaimState
import Kore.Reachability.OnePathClaim
import Kore.Reachability.Prove
