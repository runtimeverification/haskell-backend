{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

Run like this:

# Build the kore-exec and kore-profiler binaries
stack build --ghc-options "-eventlog -debug"

kore-exec +RTS -vu -RTS other-arguments 2>&1 | cat > log.out

cat log.out | kore-profiler > profiler.out

# To show only an event's children, use

cat log.out | kore-profiler --filter <event-substring> > profiler.out

-}

module Main (main) where

import Control.Monad
    ( when
    )
import qualified Data.List as List
    ( foldl'
    , intersperse
    , isInfixOf
    , isPrefixOf
    , sort
    )
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Ratio
    ( (%)
    )
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
    ( concat
    , drop
    , dropWhile
    , isPrefixOf
    , pack
    , stripStart
    , unpack
    )
import qualified Data.Text.IO as Text
    ( getLine
    , putStr
    )
import Options.Applicative
    ( InfoMod
    , Parser
    , execParser
    , fullDesc
    , header
    , help
    , helper
    , info
    , long
    , progDesc
    , strOption
    , value
    , (<**>)
    )
import System.Clock
    ( TimeSpec
    , diffTimeSpec
    , fromNanoSecs
    , toNanoSecs
    )
import System.IO
    ( hFlush
    , isEOF
    , stdout
    )
import Text.Read
    ( readMaybe
    )

import Kore.Profiler.Data
    ( ProfileEvent (ProfileEvent)
    )
import qualified Kore.Profiler.Data as ProfileEvent
    ( ProfileEvent (..)
    )

main :: IO ()
main = do
    options <- commandLineParse parseProfileOptions parserInfoModifiers
    report <- buildReport options
    Text.putStr (reportToText report)
    Text.putStr "\n"

newtype ProfileOptions = ProfileOptions { profileFilter :: String }

parseProfileOptions :: Parser ProfileOptions
parseProfileOptions =
    ProfileOptions
    <$> strOption
        (  long "filter"
        <> help "Process only events containing this string together with \
                \their subevents."
        <> value ""
        )
-- | modifiers for the Command line parser description
parserInfoModifiers :: InfoMod options
parserInfoModifiers =
    fullDesc
    <> progDesc "Computes profiling information using STDIN as the input."
    <> header "kore-profiler - a profiler for kore-exec"

commandLineParse
    :: Parser a   -- ^ options parser
    -> InfoMod a  -- ^ parser info modifiers
    -> IO a
commandLineParse commandLineParser modifiers =
    execParser
    $ info (commandLineParser <**> helper) modifiers

buildReport :: ProfileOptions -> IO (Map String EventSummary)
buildReport profileOptions = buildReportHelper 0 initialContext Map.empty
  where
    initialContext :: Context
    initialContext = Context
        { openedTagsToMultiplicity = Map.empty
        , enabled = []
        }

    buildReportHelper
        :: Integer
        -> Context
        -> Map String EventSummary
        -> IO (Map String EventSummary)
    buildReportHelper lineIndex context report = do
        eof <- isEOF
        if eof
            then return report
            else do
                when (lineIndex `mod` 100000 == 0)
                    (do
                        putStr (show lineIndex)
                        putStr "\r"
                        hFlush stdout
                    )
                line <- Text.getLine
                case parseLine line of
                    Just parsed ->
                        let fixedParsed = fixTags parsed
                            newContext =
                                updateContext profileOptions context fixedParsed
                        in buildReportHelper
                            (lineIndex + 1)
                            newContext
                            $! addProfileEventFiltered
                                context newContext fixedParsed report
                    Nothing ->
                        buildReportHelper (lineIndex + 1) context report

reportToText :: Map String EventSummary -> Text
reportToText = writeReport . removeMatchingStarts

updateContext :: ProfileOptions -> Context -> ProfileEvent -> Context
updateContext
    profileOptions
    context
    ProfileEvent { tags, end = Nothing }
  =
    withTags (withEnabled context)
  where
    withEnabled :: Context -> Context
    withEnabled c@Context { enabled } =
        c { enabled = isEnabled enabled : enabled }

    withTags :: Context -> Context
    withTags context' = foldr openTag context' tags

    openTag :: String -> Context -> Context
    openTag
        tag
        Context
            { openedTagsToMultiplicity
            , enabled = enabled@(enabledNow : _)
            }
      = Context
        { openedTagsToMultiplicity =
            if enabledNow
            then Map.insertWith (+) tag 1 openedTagsToMultiplicity
            else openedTagsToMultiplicity
        , enabled
        }
    openTag
        _
        Context { enabled = [] }
      = error "Not known if the tag is enabled."

    isEnabled :: [Bool] -> Bool
    isEnabled (True : _) = True
    isEnabled _
      | null (profileFilter profileOptions) = True
    isEnabled _ = any (profileFilter profileOptions `List.isInfixOf`) tags
updateContext
    _
    context
    ProfileEvent { tags, end = Just _ }
  =
    withoutEnabled (withoutTags context)
  where
    withoutEnabled :: Context -> Context
    withoutEnabled Context { enabled = []} =
        error "No tag opened."
    withoutEnabled
        c@Context { enabled = _ : enabledRemainder }
      =
        c { enabled = enabledRemainder }

    withoutTags :: Context -> Context
    withoutTags context' = foldr closeTag context' tags

    closeTag :: String -> Context -> Context
    closeTag
        _
        Context { enabled = [] }
      = error "No tag opened."
    closeTag
        tag
        Context
            { openedTagsToMultiplicity
            , enabled = enabled@(True : _) }
      | Map.member tag openedTagsToMultiplicity
      = Context
            { openedTagsToMultiplicity =
                Map.update closeTagCount tag openedTagsToMultiplicity
            , enabled
            }
      | otherwise = error ("Closing non-opened tag: '" ++ tag ++ "'.")
    closeTag
        _
        c@Context { enabled = False : _ }
      = c

    closeTagCount 1 = Nothing
    closeTagCount count = Just (count-1)

data Context
    = Context
        { openedTagsToMultiplicity :: !(Map.Map String Integer)
        -- ^ Contains one entry per distinct tag currently opened.
        , enabled :: ![Bool]
        -- ^ Contains one entry per event currently opened.
        }
    deriving Show

data EventSummary
    = EventSummary
        { duration :: !TimeSpec
        , count :: !Integer
        }
    deriving Show

instance Semigroup EventSummary where
    (<>)
        EventSummary
            { duration = duration1
            , count = count1
            }
        EventSummary
            { duration = duration2
            , count = count2
            }
      =
        EventSummary
            { duration =
                fromNanoSecs (toNanoSecs duration1 + toNanoSecs duration2)
            , count = count1 + count2
            }

instance Monoid EventSummary where
    mempty = EventSummary
        { duration = fromNanoSecs 0
        , count = 0
        }

parseLine :: Text -> Maybe ProfileEvent
parseLine line =
    if "ProfileEvent" `Text.isPrefixOf` event
    then readMaybe (Text.unpack event)
    else Nothing
  where
    event =
        Text.stripStart
        $ Text.drop 1
        $ Text.dropWhile (/= ':')
        $ Text.drop 1
        $ Text.dropWhile (/= ':') line

fixTags :: ProfileEvent -> ProfileEvent
fixTags event@ProfileEvent { tags } =
    event
        { ProfileEvent.tags =
            map (drop 1) $ snd $ List.foldl' concatTags ("", []) tags
        }

concatTags :: (String, [String])-> String -> (String, [String])
concatTags (first, result) second =
    (concatenated, concatenated : result)
  where
    concatenated = first ++ "-" ++ second

addProfileEventFiltered
    :: Context
    -> Context
    -> ProfileEvent
    -> Map String EventSummary
    -> Map String EventSummary
addProfileEventFiltered
    contextBefore
    contextAfter
    event
    report
  = if isEnabled contextBefore || isEnabled contextAfter
    then addProfileEvent contextAfter event report
    else report
  where
    isEnabled Context { enabled = [] } = False
    isEnabled Context { enabled = (e : _) } = e

addProfileEvent
    :: Context
    -> ProfileEvent
    -> Map String EventSummary
    -> Map String EventSummary
addProfileEvent
    context
    ProfileEvent { start, end = Just endTime, tags }
    report
  = foldr
        (addEventEndLine
            context
            (diffTimeSpec endTime start)
        )
        report
        tags
addProfileEvent
    _
    ProfileEvent { end = Nothing, tags }
    report
  = foldr addEventStartLine report tags

startPrefix :: String
startPrefix = "START "

addEventStartLine
    :: String -> Map String EventSummary -> Map String EventSummary
addEventStartLine name =
    addEvent
        (startPrefix ++ name)
        EventSummary
            { duration = fromNanoSecs 0
            , count = 1
            }

addEventEndLine
    :: Context
    -> TimeSpec
    -> String
    -> Map String EventSummary
    -> Map String EventSummary
addEventEndLine
    Context {openedTagsToMultiplicity}
    duration
    name
  =
    addEvent
        name
        EventSummary
            { duration =
                if Map.member name openedTagsToMultiplicity
                then fromNanoSecs 0
                else duration
            , count = 1
            }

addEvent
    :: String
    -> EventSummary
    -> Map String EventSummary
    -> Map String EventSummary
addEvent key event report =
    case Map.lookup key report of
        Nothing -> Map.insert key event report
        Just _ -> Map.adjust (<> event) key report
    -- Map.insertWith (<>)

removeMatchingStarts :: Map String EventSummary -> Map String EventSummary
removeMatchingStarts report =
    Map.filter nonZeroCount
    $ Map.mapWithKey (removeFinishedStart report) report
  where
    nonZeroCount :: EventSummary -> Bool
    nonZeroCount = (/= 0) . count

removeFinishedStart
    :: Map String EventSummary -> String -> EventSummary -> EventSummary
removeFinishedStart
    report
    tag
    event@EventSummary { count = startCount }
  | Just endTag <- maybeEndTag
  , Just EventSummary { count = endCount } <- Map.lookup endTag report
  =
    if endCount > startCount
    then error "Consistency error: end count is larger than start count."
    else event {count = startCount - endCount}
  where
    maybeEndTag =
        if startPrefix `List.isPrefixOf` tag
        then Just (drop (length startPrefix) tag)
        else Nothing
removeFinishedStart _ _ event = event

writeReport :: Map String EventSummary -> Text
writeReport =
    Text.concat
    . List.intersperse "\n"
    . map snd
    . List.sort
    . map writeReportLineWithKey
    . Map.toList

writeReportLineWithKey :: (String, EventSummary) -> (Integer, Text)
writeReportLineWithKey (tag, EventSummary { duration, count }) =
    ( -durationNanos
    , Text.pack $ tag
        ++ "    "
        ++ show (fromRational (durationNanos % 1000000000) :: Double)
        ++ "s    #"
        ++ show count
    )
  where
    durationNanos = toNanoSecs duration
