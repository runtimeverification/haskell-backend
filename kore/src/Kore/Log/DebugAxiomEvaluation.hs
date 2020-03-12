{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Log.DebugAxiomEvaluation
    ( AxiomEvaluationState (..)
    , DebugAxiomEvaluation (..)
    , DebugAxiomEvaluationOptions (..)
    , filterDebugAxiomEvaluation
    , mapDebugAxiomEvaluation
    , parseDebugAxiomEvaluationOptions

    -- * logging functions. Import qualified.
    , attemptAxiom
    , end
    , endNotApplicable
    , endNotApplicableConditionally
    , notEvaluated
    , notEvaluatedConditionally
    , reevaluationWhile
    , startWhile

    -- * Helpers
    , klabelIdentifier
    ) where

import Prelude.Kore

import Data.Default
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
import qualified Kore.Internal.Conditional as Conditional
    ( mapVariables
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import Kore.Internal.Symbol
    ( Symbol (Symbol)
    )
import qualified Kore.Internal.Symbol as Attribute.Symbol.DoNotUse
import Kore.Internal.TermLike
    ( pattern App_
    , TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
    ( mapVariables
    )
import Kore.Internal.Variable
    ( InternalVariable
    , Variable
    , toVariable
    )
import Kore.Step.Axiom.Identifier
    ( AxiomIdentifier
    )
import Kore.Unparser
    ( unparse
    )
import Log
    ( ActualEntry (..)
    , Entry (fromEntry, toEntry)
    , MonadLog
    , Severity (..)
    , logEntry
    , logWhile
    )
import qualified Log as Log.DoNotUse

{- | A log 'Entry' when a rule is applied.

We will log the applied rule and its unification or matching condition.

 -}
data DebugAxiomEvaluation =
    DebugAxiomEvaluation
    { identifier :: !(Maybe AxiomIdentifier)
    , secondaryIdentifier :: !(Maybe Text)
    , logPatterns :: !Bool
    , state :: !AxiomEvaluationState
    }
    deriving (Eq, Typeable)

data AxiomEvaluationState
    = Start [TermLike Variable]
    | AttemptingAxiom SourceLocation
    | NotEvaluated
    | NotEvaluatedConditionally
    | Reevaluation [Pattern Variable]
    | End [Pattern Variable]
    | EndNotApplicable
    | EndNotApplicableConditionally
    deriving Eq

instance Entry DebugAxiomEvaluation where
    entrySeverity _ = Debug
    shortDoc DebugAxiomEvaluation { identifier, state } =
        case state of
            Start _ ->
                Just $ Pretty.hsep
                    [ "While starting axiom evaluation of"
                    , Pretty.pretty identifier
                    ]
                Pretty.<+> Pretty.colon
            AttemptingAxiom _ ->
                Just $ Pretty.hsep
                    [ "While attempting axiom"
                    , Pretty.pretty identifier
                    ]
                Pretty.<+> Pretty.colon
            Reevaluation _ ->
                Just $ Pretty.hsep
                    [ "During reevaluation of"
                    , Pretty.pretty identifier
                    ]
                Pretty.<+> Pretty.colon
            _ -> Nothing

instance Pretty DebugAxiomEvaluation where
    pretty DebugAxiomEvaluation { identifier, state, logPatterns } =
        case state of
            Start arguments ->
                Pretty.sep
                    (  ["Starting:", Pretty.pretty identifier]
                    ++ if logPatterns
                        then "Arguments:" : map unparse arguments
                        else []
                    )
            AttemptingAxiom sourceLocation ->
                Pretty.sep
                    [ "Attempting axiom "
                    , Pretty.pretty sourceLocation
                    , "for:"
                    , Pretty.pretty identifier
                    ]
            NotEvaluated ->
                Pretty.sep ["Not evaluated:", Pretty.pretty identifier]
            NotEvaluatedConditionally ->
                Pretty.sep
                    [ "Under certain conditions, not evaluated:"
                    , Pretty.pretty identifier
                    ]
            Reevaluation results ->
                Pretty.sep
                    (  ["Reevaluating:", Pretty.pretty identifier]
                    ++ if logPatterns
                        then "Results:" : map unparse results
                        else []
                    )
            End results ->
                Pretty.sep
                    (  ["Ending:", Pretty.pretty identifier]
                    ++ if logPatterns
                        then "Results:" : map unparse results
                        else []
                    )
            EndNotApplicable ->
                Pretty.sep ["Ending with N/A:", Pretty.pretty identifier]
            EndNotApplicableConditionally ->
                Pretty.sep
                    ["Ending with conditional N/A:", Pretty.pretty identifier]

{- | Log the start of a term's axiom evaluation.
-}
startWhile
    :: forall log variable a
    .  (MonadLog log, InternalVariable variable)
    => [TermLike variable]
    -> Maybe AxiomIdentifier
    -> Maybe Text
    -> log a
    -> log a
startWhile arguments = logStateWhile
    (Start
        (map
            (TermLike.mapVariables (fmap toVariable) (fmap toVariable))
            arguments
        )
    )

{- | Log the end of a term's axiom evaluation.
-}
end
    :: forall log variable
    .  (MonadLog log, InternalVariable variable)
    => [Pattern variable]
    -> Maybe AxiomIdentifier
    -> Maybe Text
    -> log ()
end results = logState (End (map convertPatternVariable results))

{- | Log the end of a term's axiom evaluation.
-}
endNotApplicable
    :: forall log
    .  MonadLog log
    => Maybe AxiomIdentifier
    -> Maybe Text
    -> log ()
endNotApplicable = logState EndNotApplicable

{- | Log the end of a term's axiom evaluation.
-}
endNotApplicableConditionally
    :: forall log
    .  MonadLog log
    => Maybe AxiomIdentifier
    -> Maybe Text
    -> log ()
endNotApplicableConditionally = logState EndNotApplicableConditionally

convertPatternVariable
    :: InternalVariable variable => Pattern variable -> Pattern Variable
convertPatternVariable patt =
    Conditional.mapVariables
        TermLike.mapVariables
        (fmap toVariable)
        (fmap toVariable)
        patt

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
reevaluationWhile
    :: forall log variable a
    .  (MonadLog log, InternalVariable variable)
    => [Pattern variable]
    -> Maybe AxiomIdentifier
    -> Maybe Text
    -> log a
    -> log a
reevaluationWhile results =
    logStateWhile (Reevaluation (map convertPatternVariable results))

attemptAxiom
    :: MonadLog log
    => SourceLocation
    -> Maybe AxiomIdentifier
    -> Maybe Text
    -> log ()
attemptAxiom sourceLocation = logState (AttemptingAxiom sourceLocation)

logStateWhile
    :: MonadLog log
    => AxiomEvaluationState
    -> Maybe AxiomIdentifier
    -> Maybe Text
    -> log a
    -> log a
logStateWhile state identifier secondaryIdentifier action =
    logWhile
        DebugAxiomEvaluation
            { identifier
            , secondaryIdentifier
            , logPatterns = False
            , state
            }
        action

logState
    :: MonadLog log
    => AxiomEvaluationState
    -> Maybe AxiomIdentifier
    -> Maybe Text
    -> log ()
logState state identifier secondaryIdentifier =
    logEntry
        DebugAxiomEvaluation
            { identifier
            , secondaryIdentifier
            , logPatterns = False
            , state
            }

{- | Options (from the command-line) specifying when to log specific axiom
applications.

See also: 'parseDebugAxiomEvaluationOptions'

 -}
data DebugAxiomEvaluationOptions =
    DebugAxiomEvaluationOptions
        { debugAxiomEvaluation :: !(Set Text)
        , debugAxiomEvaluationPatterns :: !Bool
        }
    deriving (Eq, Show)

instance Default DebugAxiomEvaluationOptions where
    def = mempty

instance Semigroup DebugAxiomEvaluationOptions where
    (<>) a b =
        DebugAxiomEvaluationOptions
            { debugAxiomEvaluation = on (<>) debugAxiomEvaluation a b
            , debugAxiomEvaluationPatterns =
                on (||) debugAxiomEvaluationPatterns a b
            }

instance Monoid DebugAxiomEvaluationOptions where
    mempty = DebugAxiomEvaluationOptions
        { debugAxiomEvaluation = mempty
        , debugAxiomEvaluationPatterns = False
        }

parseDebugAxiomEvaluationOptions :: Parser DebugAxiomEvaluationOptions
parseDebugAxiomEvaluationOptions =
    DebugAxiomEvaluationOptions
    <$> (Set.fromList <$> many parseId)
    <*> patterns
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
    patterns =
        Options.switch
            (  Options.long "debug-simplification-axiom-patterns"
            <> Options.help
                (  "Log arguments and results for "
                <> "SIMPLIFICATION_IDENTIFIER's evaluation."
                )
            )

{- | Function to modify a 'LogAction' to display selected applied rules.
 -}
filterDebugAxiomEvaluation
    :: DebugAxiomEvaluationOptions
    -> ActualEntry
    -> Bool
filterDebugAxiomEvaluation
    debugAxiomEvaluationOptions
    ActualEntry { actualEntry }
  =
    fromMaybe False findAxiomEvaluation
  where
    findAxiomEvaluation :: Maybe Bool
    findAxiomEvaluation = do
        DebugAxiomEvaluation
            { identifier, secondaryIdentifier }
                <- fromEntry actualEntry
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

mapDebugAxiomEvaluation
    :: DebugAxiomEvaluationOptions
    -> ActualEntry
    -> ActualEntry
mapDebugAxiomEvaluation
    debugAxiomEvaluationOptions
    entry@ActualEntry { actualEntry }
  =
    fromMaybe entry mapAxiomEvaluation
  where
    mapAxiomEvaluation :: Maybe ActualEntry
    mapAxiomEvaluation = do
        axiomEntry@DebugAxiomEvaluation { logPatterns } <- fromEntry actualEntry
        return entry
            { actualEntry =
                toEntry axiomEntry
                    {logPatterns = logPatterns || debugAxiomEvaluationPatterns}
            }

    DebugAxiomEvaluationOptions { debugAxiomEvaluationPatterns } =
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
