{- |
Copyright   : (c) Runtime Verification, 2021
License     : BSD-3-Clause
-}
module Kore.Log.WarnClaimRHSIsBottom (
    WarnClaimRHSIsBottom (..),
    warnClaimRHSIsBottom,
) where

import Kore.Attribute.SourceLocation
import Kore.Rewrite.ClaimPattern
import Log
import Prelude.Kore
import Pretty (
    Pretty,
 )
import qualified Pretty

newtype WarnClaimRHSIsBottom = WarnClaimRHSIsBottom {claim :: ClaimPattern}
    deriving stock (Show)

instance Pretty WarnClaimRHSIsBottom where
    pretty WarnClaimRHSIsBottom{claim} =
        Pretty.hsep
            [ "The right-hand side of the claim is bottom:"
            , prettySourceLocation claim
            ]

instance Entry WarnClaimRHSIsBottom where
    entrySeverity _ = Warning
    helpDoc _ = "warn when the right-hand side of a claim is bottom"
    oneLineDoc WarnClaimRHSIsBottom{claim} = prettySourceLocation claim

prettySourceLocation :: ClaimPattern -> Pretty.Doc ann
prettySourceLocation = Pretty.pretty @SourceLocation . from

warnClaimRHSIsBottom ::
    MonadLog log =>
    ClaimPattern ->
    log ()
warnClaimRHSIsBottom = logEntry . WarnClaimRHSIsBottom
