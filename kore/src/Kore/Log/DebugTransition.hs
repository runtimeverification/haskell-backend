{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Log.DebugTransition (
    DebugTransition (..),
    debugBeforeTransition,
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

data DebugTransition
    = DebugAfterTransition
        (Maybe (ClaimState SomeClaim))
        Prim
        [SourceLocation]
    | DebugBeforeTransition
        (ClaimState SomeClaim)
        Prim
    deriving stock (Show)

instance Pretty DebugTransition where
    pretty (DebugAfterTransition result transition appliedRules) =
        Pretty.vsep $ concat
            [ 
                [ "Applied the following transition:"
                , Pretty.indent 4 (pretty transition)
                ]
            , prettyRules
            ,   
                [ "Resulting in:"
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

    pretty (DebugBeforeTransition proofState transition) =
        Pretty.vsep
            [ "Reached proof state with the following configuration:"
            , Pretty.indent 4 (pretty proofState)
            , "To which the following transition will be applied:"
            , Pretty.indent 4 (pretty transition)
            ]

instance Entry DebugTransition where
    entrySeverity _ = Debug
    helpDoc _ = "log proof state"
    oneLineDoc (DebugAfterTransition _proofState transition appliedRules) =
        Just $ 
            transitionHeader 
                <> Pretty.hsep (pretty <$> appliedRules)
      where
        transitionHeader = case appliedRules of
            [] -> pretty transition
            _otherwise -> pretty transition <> ": "
    oneLineDoc (DebugBeforeTransition _proofState transition) =
        Just (pretty transition)

debugBeforeTransition ::
    MonadLog log =>
    ClaimState SomeClaim ->
    Prim ->
    log ()
debugBeforeTransition proofState transition =
    logEntry $ DebugBeforeTransition proofState transition

debugAfterTransition ::
    MonadLog log =>
    From rule SourceLocation =>
    ClaimState SomeClaim ->
    Prim ->
    [rule] ->
    log ()
debugAfterTransition proofState transition rules =
    logEntry $
        DebugAfterTransition
            (Just proofState)
            transition
            appliedRules
  where
    appliedRules = map from rules

debugFinalTransition ::
    MonadLog log =>
    Prim ->
    log ()
debugFinalTransition transition =
    logEntry $
        DebugAfterTransition
            Nothing
            transition
            []
