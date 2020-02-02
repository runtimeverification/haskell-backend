{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Log.DebugAxiomEvaluation
    ( AxiomEvaluationState (..)
    , DebugAxiomEvaluation (..)
    , DebugAxiomEvaluationOptions (..)
    , filterDebugAxiomEvaluation
    , parseDebugAxiomEvaluationOptions

    -- * logging functions. Import qualified.
    , attemptAxiom
    , end
    , notEvaluated
    , notEvaluatedConditionally
    , reevaluation
    , start

    -- * Helpers
    , klabelIdentifier
    ) where

import Prelude.Kore

import Control.Applicative
    ( Alternative (..)
    )
import Data.Default
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

import Kore.Attribute.SourceLocation as Attribute
    ( SourceLocation
    )
import qualified Kore.Attribute.Symbol as Attribute
    ( Symbol (Symbol)
    )
import qualified Kore.Attribute.Symbol as Attribute.Symbol.DoNotUse
import qualified Kore.Attribute.Symbol.Klabel as Attribute
    ( Klabel (Klabel)
    )
import Kore.Internal.Symbol
    ( Symbol (Symbol)
    )
import qualified Kore.Internal.Symbol as Attribute.Symbol.DoNotUse
import Kore.Internal.TermLike
    ( pattern App_
    , TermLike
    )
import Kore.Step.Axiom.Identifier
    ( AxiomIdentifier
    )
import Log
    ( Entry (fromEntry)
    , MonadLog
    , Severity (..)
    , SomeEntry
    , logM
    )
import qualified Log as Log.DoNotUse

{- | A log 'Entry' when a rule is applied.

We will log the applied rule and its unification or matching condition.

 -}
data DebugAxiomEvaluation =
    DebugAxiomEvaluation
    { identifier :: !(Maybe AxiomIdentifier)
    , secondaryIdentifier :: !(Maybe Text)
    , state :: !AxiomEvaluationState
    }
    deriving (Eq, Typeable)

data AxiomEvaluationState
    = Start
    | AttemptingAxiom SourceLocation
    | NotEvaluated
    | NotEvaluatedConditionally
    | Reevaluation
    | End
    deriving Eq

instance Entry DebugAxiomEvaluation where
    entrySeverity _ = Debug

instance Pretty DebugAxiomEvaluation where
    pretty DebugAxiomEvaluation { identifier, state } =
        case state of
            Start ->
                Pretty.sep ["Starting:", Pretty.pretty identifier]
            AttemptingAxiom sourceLocation ->
                Pretty.sep
                    [ "Attempting axiom "
                    , Pretty.pretty sourceLocation
                    , "for:"
                    , Pretty.pretty identifier
                    ]
            NotEvaluated ->
                Pretty.sep ["No results for:", Pretty.pretty identifier]
            NotEvaluatedConditionally ->
                Pretty.sep
                    [ "Under certain conditions, no results for:"
                    , Pretty.pretty identifier
                    ]
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
    -> Maybe Text
    -> log ()
start = logState Start

{- | Log the end of a term's axiom evaluation.
-}
end
    :: forall log
    .  MonadLog log
    => Maybe AxiomIdentifier
    -> Maybe Text
    -> log ()
end = logState End

{- | Log the start of a term's axiom evaluation.
-}
notEvaluated
    :: forall log
    .  MonadLog log
    => Maybe AxiomIdentifier
    -> Maybe Text
    -> log ()
notEvaluated = logState NotEvaluated

{- | Log the start of a term's axiom evaluation.
-}
notEvaluatedConditionally
    :: forall log
    .  MonadLog log
    => Maybe AxiomIdentifier
    -> Maybe Text
    -> log ()
notEvaluatedConditionally = logState NotEvaluatedConditionally

{- | Log the start of a term's axiom evaluation.
-}
reevaluation
    :: forall log
    .  MonadLog log
    => Maybe AxiomIdentifier
    -> Maybe Text
    -> log ()
reevaluation = logState Reevaluation

attemptAxiom
    :: MonadLog log
    => SourceLocation
    -> Maybe AxiomIdentifier
    -> Maybe Text
    -> log ()
attemptAxiom sourceLocation = logState (AttemptingAxiom sourceLocation)

logState
    :: MonadLog log
    => AxiomEvaluationState
    -> Maybe AxiomIdentifier
    -> Maybe Text
    -> log ()
logState state identifier secondaryIdentifier =
    logM DebugAxiomEvaluation
        { identifier
        , secondaryIdentifier
        , state
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

instance Default DebugAxiomEvaluationOptions where
    def = mempty

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
                (  "Log every rule applied for the "
                <> "SIMPLIFICATION_IDENTIFIER."
                )
            )

{- | Function to modify a 'LogAction' to display selected applied rules.
 -}
filterDebugAxiomEvaluation
    :: DebugAxiomEvaluationOptions
    -> SomeEntry
    -> Bool
filterDebugAxiomEvaluation
    debugAxiomEvaluationOptions
    entry
  =
    fromMaybe False findAxiomEvaluation
  where
    findAxiomEvaluation :: Maybe Bool
    findAxiomEvaluation = do
        DebugAxiomEvaluation
            { identifier, secondaryIdentifier }
                <- fromEntry entry
        let textIdentifier :: Maybe Text
            textIdentifier =
                Text.pack . show . Pretty.pretty <$> identifier

            isSelectedIdentifier :: Text -> Bool
            isSelectedIdentifier toCheck =
                Set.member toCheck debugAxiomEvaluation

            isSelected :: Bool
            isSelected =
                any
                    isSelectedIdentifier
                    (catMaybes [textIdentifier, secondaryIdentifier])

        return isSelected

    DebugAxiomEvaluationOptions { debugAxiomEvaluation } =
        debugAxiomEvaluationOptions

klabelIdentifier :: TermLike variable -> Maybe Text
klabelIdentifier
    (App_
        Symbol
            {symbolAttributes = Attribute.Symbol
                {klabel = Attribute.Klabel {getKlabel}}
            }
        _
    )
  =
    getKlabel
klabelIdentifier _ = Nothing
