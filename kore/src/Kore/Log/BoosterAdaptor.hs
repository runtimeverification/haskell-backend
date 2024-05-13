{- |
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
-}
module Kore.Log.BoosterAdaptor (
    renderStandardPretty,
    renderOnelinePretty,
    renderJson,
    koreSomeEntryLogAction,
    withLogger,
    WithTimestamp (..),
    module KoreLogOptions,
    module Log,
    ExeName (..),
) where

import Colog qualified
import Control.Monad.Cont (
    ContT (..),
    runContT,
 )
import Data.Aeson qualified as JSON
import Data.Aeson.KeyMap qualified as JSON
import Data.Aeson.Text qualified as JSON
import Data.Functor.Contravariant (
    contramap,
 )
import Data.Text (
    Text,
 )
import Data.Text.Lazy qualified as LazyText
import Data.Vector qualified as Vec
import Kore.Log (WithTimestamp (..), swappableLogger, withTimestamp)
import Kore.Log qualified as Log
import Kore.Log.KoreLogOptions as KoreLogOptions
import Kore.Log.Registry (
    lookupTextFromTypeWithError,
    typeOfSomeEntry,
 )
import Log
import Prelude.Kore
import Pretty qualified
import System.Clock (
    TimeSpec (..),
    diffTimeSpec,
    toNanoSecs,
 )

withLogger ::
    KoreLogOptions ->
    (LogAction IO SomeEntry -> IO a) ->
    IO a
withLogger koreLogOptions = runContT $ do
    mainLogger <- ContT $ withMainLogger koreLogOptions
    let KoreLogOptions{exeName, debugSolverOptions} = koreLogOptions
    smtSolverLogger <- ContT $ Log.withSmtSolverLogger exeName debugSolverOptions
    return $ mainLogger <> smtSolverLogger

withMainLogger ::
    KoreLogOptions ->
    (LogAction IO SomeEntry -> IO a) ->
    IO a
withMainLogger koreLogOptions = runContT $ do
    pure
        . Log.koreLogTransformer koreLogOptions
        . Log.koreLogFilters koreLogOptions
        $ case logType koreLogOptions of
            LogProxy logAction -> logAction
            ltype -> error ("Unexpected log type " <> show ltype)

koreSomeEntryLogAction ::
    MonadIO m =>
    -- | how to render a timestamped 'SomeEntry' into Text
    (WithTimestamp -> Text) ->
    -- | filter log entries, applies BEFORE rendering to text
    (SomeEntry -> Bool) ->
    -- | filter log entries, applies AFTER rendering to text
    (Text -> Bool) ->
    LogAction m Text ->
    LogAction m SomeEntry
koreSomeEntryLogAction renderer earlyFilter lateFilter textLogAction =
    textLogAction
        & Colog.cfilter lateFilter
        & contramap renderer
        & Colog.cmapM withTimestamp
        & Colog.cfilter earlyFilter

renderJson :: ExeName -> TimeSpec -> TimestampsSwitch -> WithTimestamp -> Text
renderJson _exeName _startTime _timestampSwitch (WithTimestamp e@(SomeEntry context actualEntry) _entryTime) =
    LazyText.toStrict . JSON.encodeToLazyText $ json
  where
    jsonContext =
        foldr
            ( \(SomeEntry _ c) cs -> case oneLineContextJson c of
                JSON.Array cs' -> cs' <> cs
                -- JSON.Object o | Just (JSON.Array cs') <- JSON.lookup "context" o -> cs' <> cs
                j -> Vec.cons j cs
            )
            mempty
            (context <> [e])

    json = case oneLineJson actualEntry of
        JSON.Object o
            | Just (JSON.Array ctxt) <- JSON.lookup "context" o ->
                JSON.Object $ JSON.insert "context" (JSON.Array $ jsonContext <> ctxt) o
        other ->
            JSON.object
                [ "message" JSON..= other
                , "context" JSON..= jsonContext
                ]

renderOnelinePretty :: ExeName -> TimeSpec -> TimestampsSwitch -> WithTimestamp -> Text
renderOnelinePretty _exeName _startTime _timestampSwitch (WithTimestamp entry@(SomeEntry entryContext _actualEntry) _entryTime) =
    let cs =
            (entryContext <> [entry])
                & concatMap (map Pretty.brackets . (\(SomeEntry _ e) -> oneLineContextDoc e))
        leaf = oneLineDoc entry
     in mconcat (cs <> [leaf])
            & Pretty.layoutPretty Pretty.defaultLayoutOptions{Pretty.layoutPageWidth = Pretty.Unbounded}
            & Pretty.renderText

renderStandardPretty :: ExeName -> TimeSpec -> TimestampsSwitch -> WithTimestamp -> Text
renderStandardPretty exeName startTime timestampSwitch (WithTimestamp entry@(SomeEntry entryContext actualEntry) entryTime) =
    prettyActualEntry
        & Pretty.layoutPretty Pretty.defaultLayoutOptions
        & Pretty.renderText
  where
    timestamp =
        case timestampSwitch of
            TimestampsDisable -> Nothing
            TimestampsEnable ->
                Just . Pretty.brackets . Pretty.pretty $
                    toMicroSecs (diffTimeSpec startTime entryTime)
    toMicroSecs = (`div` 1000) . toNanoSecs
    exeName' = Pretty.pretty exeName <> Pretty.colon
    prettyActualEntry =
        Pretty.vsep . concat $
            [ [header]
            , indent <$> [longDoc actualEntry]
            , context'
            ]
      where
        header =
            (Pretty.hsep . catMaybes)
                [ Just exeName'
                , timestamp
                , Just severity'
                , Just (Pretty.parens $ type' entry)
                ]
                <> Pretty.colon
        severity' = prettySeverity (entrySeverity actualEntry)
        type' e =
            Pretty.pretty $
                lookupTextFromTypeWithError $
                    typeOfSomeEntry e
        context' =
            (entry : entryContext)
                & reverse
                & mapMaybe (\e -> (,type' e) <$> contextDoc e)
                & prettyContext
        prettyContext =
            \case
                [] -> []
                xs -> ("Context" <> Pretty.colon) : (indent <$> mkContext xs)

        mkContext =
            \case
                [] -> []
                [(doc, typeName)] ->
                    [Pretty.hsep [Pretty.parens typeName, doc]]
                (doc, typeName) : xs -> (Pretty.hsep [Pretty.parens typeName, doc]) : (indent <$> (mkContext xs))

    indent = Pretty.indent 4
