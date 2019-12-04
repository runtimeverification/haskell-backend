{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Logger.DebugAxiomEvaluation
    ( AxiomEvaluationState (..)
    , DebugAxiomEvaluation (..)
    , DebugAxiomEvaluationOptions (..)
    , filterDebugAxiomEvaluation
    , parseDebugAxiomEvaluationOptions

    -- * logging functions. Import qualified.
    , end
    , notEvaluated
    , reevaluation
    , start
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import Data.Function
    ( on
    )
import Data.Maybe
    ( catMaybes
    , fromMaybe
    )
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
    ( pack
    )
import Data.Text.Prettyprint.Doc
    ( Pretty
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import Data.Typeable
import Options.Applicative
    ( Parser
    )
import qualified Options.Applicative as Options

import Kore.Logger
    ( Entry (fromEntry, toEntry)
    , LogAction (LogAction)
    , MonadLog
    , Severity (..)
    , SomeEntry
    , WithScope (WithScope)
    , logM
    , unLogAction
    )
import qualified Kore.Logger as Log.DoNotUse
import Kore.Step.Axiom.Identifier
    ( AxiomIdentifier
    )

{- | A log 'Entry' when a rule is applied.

We will log the applied rule and its unification or matching condition.

 -}
data DebugAxiomEvaluation =
    DebugAxiomEvaluation
    { identifier :: !(Maybe AxiomIdentifier)
    , secondaryIdentifier :: Maybe Text
    , state :: !AxiomEvaluationState
    , severity :: !Severity
    }
    deriving (Eq, Typeable)

data AxiomEvaluationState
    = Start
    | NotEvaluated
    | Reevaluation
    | End
    deriving Eq

instance Entry DebugAxiomEvaluation where
    entrySeverity DebugAxiomEvaluation {severity} = severity

    entryScopes _ = Set.singleton "AxiomEvaluation"

instance Pretty DebugAxiomEvaluation where
    pretty DebugAxiomEvaluation { identifier, state } =
        case state of
            Start ->
                Pretty.sep ["Starting:", Pretty.pretty identifier]
            NotEvaluated ->
                Pretty.sep ["No results for:", Pretty.pretty identifier]
            Reevaluation ->
                Pretty.sep ["Reevaluating:", Pretty.pretty identifier]
            End ->
                Pretty.sep ["Ending:", Pretty.pretty identifier]

{- | Log the start of a term's axiom evaluation.
-}
start
    :: forall log
    .  MonadLog log
    => Maybe AxiomIdentifier
    -> log ()
start = logState Start

{- | Log the end of a term's axiom evaluation.
-}
end
    :: forall log
    .  MonadLog log
    => Maybe AxiomIdentifier
    -> log ()
end = logState End

{- | Log the start of a term's axiom evaluation.
-}
notEvaluated
    :: forall log
    .  MonadLog log
    => Maybe AxiomIdentifier
    -> log ()
notEvaluated = logState NotEvaluated

{- | Log the start of a term's axiom evaluation.
-}
reevaluation
    :: forall log
    .  MonadLog log
    => Maybe AxiomIdentifier
    -> log ()
reevaluation = logState Reevaluation

logState
    :: MonadLog log
    => AxiomEvaluationState
    -> Maybe AxiomIdentifier
    -> log ()
logState state identifier =
    logM DebugAxiomEvaluation
        { identifier
        , secondaryIdentifier = Nothing
        , state
        , severity = Info
        }

{- | Options (from the command-line) specifying when to log specific axiom
applications.

See also: 'parseDebugAxiomEvaluationOptions'

 -}
newtype DebugAxiomEvaluationOptions =
    DebugAxiomEvaluationOptions
        { debugAxiomEvaluation :: Set Text
        }
    deriving (Eq, Show)

instance Semigroup DebugAxiomEvaluationOptions where
    (<>) a b =
        DebugAxiomEvaluationOptions
            { debugAxiomEvaluation = on (<>) debugAxiomEvaluation a b }

instance Monoid DebugAxiomEvaluationOptions where
    mempty = DebugAxiomEvaluationOptions mempty

parseDebugAxiomEvaluationOptions :: Parser DebugAxiomEvaluationOptions
parseDebugAxiomEvaluationOptions =
    DebugAxiomEvaluationOptions
    <$> (Set.fromList <$> many parseId)
  where
    parseId =
        Options.strOption
            (  Options.metavar "SIMPLIFICATION_IDENTIFIER"
            <> Options.long "debug-simplification-axiom"
            <> Options.help
                (  "Log at the info level every rule applied for the "
                <> "SIMPLIFICATION_IDENTIFIER."
                )
            )

{- | Modify a 'LogAction' to display selected applied rules.

The "base" 'LogAction' is used to log the applied rule whenever it matches the
rules specified by 'DebugAppliedRuleOptions'. All other entries are forwarded to
the "fallback" 'LogAction'.

 -}
filterDebugAxiomEvaluation
    :: DebugAxiomEvaluationOptions
    -> LogAction log SomeEntry  -- ^ base 'LogAction'
    -> LogAction log SomeEntry
filterDebugAxiomEvaluation
    debugAxiomEvaluationOptions
    baseLogAction
  =
    LogAction $ \entry ->
        unLogAction baseLogAction (fixEntry entry)
  where
    fixEntry :: SomeEntry -> SomeEntry
    fixEntry entry =
        fromMaybe entry (fixAxiomEvaluation entry <|> throughScope entry)

    throughScope :: SomeEntry -> Maybe SomeEntry
    throughScope entry = do
        WithScope { entry = entry' } <- fromEntry entry
        return (fixEntry entry')

    fixAxiomEvaluation :: SomeEntry -> Maybe SomeEntry
    fixAxiomEvaluation entry = do
        axiomEvaluation@DebugAxiomEvaluation
            { identifier, secondaryIdentifier, severity = Info }
                <- fromEntry entry
        let textIdentifier :: Maybe Text
            textIdentifier = (Text.pack . show) <$> identifier

            isSelectedIdentifier :: Text -> Bool
            isSelectedIdentifier toCheck =
                Set.member toCheck debugAxiomEvaluation

            isSelected :: Bool
            isSelected =
                any
                    isSelectedIdentifier
                    (catMaybes [textIdentifier, secondaryIdentifier])

        if isSelected
            then return entry
            else return (toEntry axiomEvaluation {severity = Debug})

    DebugAxiomEvaluationOptions { debugAxiomEvaluation } =
        debugAxiomEvaluationOptions
