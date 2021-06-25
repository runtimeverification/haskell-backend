{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Log.DebugAfterTransition (
    DebugAfterTransition (..),
    debugAfterTransition,
    debugFinalTransition,
) where

import Kore.Attribute.Axiom (
    SourceLocation,
 )
import Kore.Reachability.ClaimState (
    ClaimState,
 )
import Kore.Reachability.Prim (
    Prim (..),
 )
import Kore.Reachability.SomeClaim (
    SomeClaim (..),
 )
import Log
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import qualified Pretty

data DebugAfterTransition = DebugAfterTransition
    { result       :: Maybe (ClaimState SomeClaim)
    , transition   :: Prim
    , appliedRules :: [SourceLocation]
    }
    deriving stock (Show)

instance Pretty DebugAfterTransition where
    pretty
        DebugAfterTransition
            { result
            , transition
            , appliedRules
            } =
            Pretty.vsep $ concat
                [ [ "Applied the following transition:"
                  , Pretty.indent 4 (pretty transition)
                  ]
                , prettyRules
                , [ "Resulting in:"
                  , Pretty.indent 4 (maybe "Terminal state." pretty result)
                  ]
                ]
      where
        -- match behavior of DebugAppliedRewriteRules
        prettyRules = case appliedRules of
            [] -> ["No rules were applied."]
            rules ->
                ["The rules at following locations were applied:"]
                    <> fmap pretty rules

instance Entry DebugAfterTransition where
    entrySeverity _ = Debug
    helpDoc _ = "log proof state"
    oneLineDoc DebugAfterTransition{transition, appliedRules} =
        Just $ transitionHeader 
            <> Pretty.hsep (pretty <$> appliedRules)
      where
        transitionHeader = case appliedRules of
            [] -> pretty transition
            _otherwise -> pretty transition <> ": "

debugAfterTransition ::
    MonadLog log =>
    From rule SourceLocation =>
    ClaimState SomeClaim ->
    Prim ->
    [rule] ->
    log ()
debugAfterTransition proofState transition rules =
    logEntry
        DebugAfterTransition
            { result = Just proofState
            , transition
            , appliedRules
            }
  where
    appliedRules = map from rules

debugFinalTransition ::
    MonadLog log =>
    Prim ->
    log ()
debugFinalTransition transition =
    logEntry
        DebugAfterTransition
            { result = Nothing
            , transition
            , appliedRules = []
            }
