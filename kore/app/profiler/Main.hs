{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

Run like this:

# Build the kore-exec and kore-profiler binaries
stack build --ghc-options "-eventlog -debug"

kore-exec +RTS -vu -RTS other-arguments 2>&1 | cat > log.out

cat log.out | kore-profiler > profiler.out
-}

module Main (main) where

import           Control.Monad
                 ( when )
import qualified Data.List as List
                 ( foldl', intersperse, isPrefixOf, sort )
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Ratio
                 ( (%) )
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
                 ( concat, drop, dropWhile, isPrefixOf, pack, stripStart,
                 unpack )
import qualified Data.Text.IO as Text
                 ( getLine, putStr )
import           System.IO
                 ( hFlush, isEOF, stdout )
import           Text.Read
                 ( readMaybe )

import           Kore.Profiler.Data
                 ( ProfileEvent (ProfileEvent) )
import qualified Kore.Profiler.Data as ProfileEvent
                 ( ProfileEvent (..) )

main :: IO ()
main = do
    report <- buildReport
    Text.putStr (reportToText report)
    Text.putStr "\n"

buildReport :: IO (Map String EventSummary)
buildReport = buildReportHelper 0 initialContext Map.empty
  where
    initialContext :: Context
    initialContext = Context { openedTagsToMultiplicity = Map.empty }

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
                            newContext = updateContext context fixedParsed
                        in buildReportHelper
                            (lineIndex + 1)
                            newContext
                            $! addProfileEvent newContext fixedParsed report
                    Nothing ->
                        buildReportHelper (lineIndex + 1) context report

reportToText :: Map String EventSummary -> Text
reportToText = writeReport . removeMatchingStarts

updateContext :: Context -> ProfileEvent -> Context
updateContext
    context
    ProfileEvent { tags, endPico = Nothing }
  =
    foldr openTag context tags
  where
    openTag :: String -> Context -> Context
    openTag
        tag
        Context { openedTagsToMultiplicity }
      = Context
        { openedTagsToMultiplicity =
            Map.insertWith (+) tag 1 openedTagsToMultiplicity
        }
updateContext
    context
    ProfileEvent { tags, endPico = Just _ }
  = foldr closeTag context tags
  where
    closeTag :: String -> Context -> Context
    closeTag
        tag
        Context { openedTagsToMultiplicity }
      | Map.member tag openedTagsToMultiplicity
      = Context
            { openedTagsToMultiplicity =
                Map.update closeTagCount tag openedTagsToMultiplicity
            }
      | otherwise = error ("Closing non-opened tag: '" ++ tag ++ "'.")

    closeTagCount 1 = Nothing
    closeTagCount count = Just (count-1)

newtype Context = Context { openedTagsToMultiplicity :: Map.Map String Integer }
    deriving Show

data EventSummary
    = EventSummary
        { durationPico :: !Integer
        , count :: !Integer
        }

instance Semigroup EventSummary where
    (<>)
        EventSummary
            { durationPico = durationPico1
            , count = count1
            }
        EventSummary
            { durationPico = durationPico2
            , count = count2
            }
      =
        EventSummary
            { durationPico = durationPico1 + durationPico2
            , count = count1 + count2
            }

instance Monoid EventSummary where
    mempty = EventSummary
        { durationPico = 0
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

addProfileEvent
    :: Context
    -> ProfileEvent
    -> Map String EventSummary
    -> Map String EventSummary
addProfileEvent
    context
    ProfileEvent { startPico, endPico = Just end, tags }
    report
  = foldr
        (addEventEndLine context (end - startPico))
        report
        tags
addProfileEvent
    _
    ProfileEvent { endPico = Nothing, tags }
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
            { durationPico = 0
            , count = 1
            }

addEventEndLine
    :: Context
    -> Integer
    -> String
    -> Map String EventSummary
    -> Map String EventSummary
addEventEndLine
    Context {openedTagsToMultiplicity}
    durationPico
    name
  =
    addEvent
        name
        EventSummary
            { durationPico =
                if Map.member name openedTagsToMultiplicity
                then 0
                else durationPico
            , count = 1
            }

addEvent
    :: String
    -> EventSummary
    -> Map String EventSummary
    -> Map String EventSummary
addEvent key value report =
    case Map.lookup key report of
        Nothing -> Map.insert key value report
        Just _ -> Map.adjust (<> value) key report
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
writeReportLineWithKey (tag, EventSummary { durationPico, count }) =
    ( -durationPico
    , Text.pack $ tag
        ++ "    "
        ++ show (fromRational (durationPico % 1000000000000) :: Double)
        ++ "s    #"
        ++ show count
    )
