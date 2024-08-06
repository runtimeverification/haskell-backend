{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

{-
To use this script, first compile it with
```
$ ghc -package bytestring -package regex -O2
```

-}

module Main where

import Control.Applicative
import Control.Monad
import Data.ByteString.Char8 (ByteString)
import Data.ByteString.Char8 qualified as BS
import Data.Data
import Data.Either
import Data.Maybe (fromMaybe, mapMaybe, maybeToList)
import Data.Tuple
import Debug.Trace
import Text.Printf
import Text.Read (readMaybe)
import Text.Regex.Base
import Text.Regex.PCRE
import System.Environment

main = do
    let process =
            asTable
            . map (either error id . parseWith parseReqRec)
            . splitOn isReq
            . mapMaybe tokenise
            . BS.lines
    args <- getArgs
    case args of
        [] -> BS.putStrLn . process =<< BS.getContents
        [f] -> BS.putStrLn =<< process <$> BS.readFile f
        fs -> mapM_ (\f -> BS.putStrLn =<< ((BS.pack f <> "\n") <>) . process <$> BS.readFile f) fs

{-
Parses (textual) timing information into per-request timing information
A json based version of this could be added to process-logs

NB: Timing information should not be collected from (full) context
logs, the overhead is too high.

Parsing:
- A parser works on a token stream to assemble a request timing record.
- It is unclear what to do about out-of-order messages.

-}

{-
Tokenisation: Each log line can become a token, carrying timing
information about a step of the execution.
-}
type RequestId = ByteString

data RequestKind
    = ExecuteM
    | ImpliesM
    | SimplifyM
    | AddModuleM
--    | LLVMCall -- hack
    deriving stock (Eq, Read, Show)

data AbortKind
    = Aborted
    | Stuck
    | Branching
    deriving stock (Eq, Read, Show)

data Line
    = NodeRequest RequestId
    | RequestTime RequestId RequestKind Time Time
    | AbortMarker RequestId AbortKind
    deriving stock (Eq, Show)

newtype Time = Time Double
    deriving newtype (Eq, Ord, Show, Num, Fractional, Real, RealFrac)

instance Read Time where
    readsPrec _ input =
        maybeToList $ do
        let (number, suffix) = span (`elem` '.':['0'..'9']) input
        multiplier <-
            case suffix of
                "s" -> pure 1.0
                "ms" -> pure 1e-3
                "\206\188s" -> pure 1e-6 -- μs, encoded in a byte string
                "\188s" -> pure 1e-6 -- hack: μs without first byte
                _other -> fail "invalid suffix"
        dbl <- readMaybe number
        pure (Time $ dbl * multiplier, "")

tokenise :: ByteString -> Maybe Line
tokenise input = asum $ map (uncurry tryMatch) matchers
  where
    readBS :: Read a => ByteString -> a
    readBS = read . BS.unpack

    groupsFrom :: ByteString -> Maybe [ByteString]
    groupsFrom regex =
        case input =~ regex of
            ("", "", "", []) -> Nothing -- empty input
            ("", all, "", groups) | all == input -> Just groups
            (_unmatched :: (ByteString, ByteString, ByteString, [ByteString])) -> Nothing

    tryMatch :: ByteString -> ([ByteString] -> Line) -> Maybe Line
    tryMatch regex mkLine = mkLine <$> groupsFrom regex

    matchers =
        [ (nodeRequest, NodeRequest . head . tail)
        , (requestTime, mkRequestTime)
        , (abortMarker, mkAbortMarker)
        ]

    mkRequestTime :: [ByteString] -> Line
    mkRequestTime [_, request, kind, time, _, kore, _] =
        RequestTime request (readBS kind) (readBS time) (readBS kore)
    mkRequestTime other = error $ "not request time data: " <> show other

    mkAbortMarker :: [ByteString] -> Line
    mkAbortMarker [_, request, kind] =
        AbortMarker request (readBS kind)
    mkAbortMarker other = error $ "Not abort marker data: " <> show other

    onHead :: (a -> b) -> [a] -> b
    onHead f [] = error (show input <> ": missing argument after matching")
    onHead f [x] = f x
    onHead f (x:_) = f x -- could throw an error..

pykPrefix, nodeRequest, requestTime, abortMarker :: ByteString
pykPrefix =
    "^(INFO:pyk\\.kore\\.rpc:\\[PID=[0-9]*\\]\\[stde\\] )?"
nodeRequest =
    pykPrefix <> contexts ["proxy"] <> "Processing request (.*)$"
requestTime =
    pykPrefix <>
        contexts ["request (.*)", "proxy", "timing"] <>
        "Performed (.*) in ([0-9.]*(m|\206\188|)s) \\(([0-9.]*(m|\206\188|)?s) kore time\\)$"
abortMarker =
    pykPrefix <>
        contexts ["request (.*)", "proxy"] <>
        "Booster (Aborted|Stuck) at Depth .*"

contexts :: [ByteString] -> ByteString
contexts [] = " "
contexts (c:cs) = "\\[" <> c <> "\\]" <> contexts cs

----------------------------------------
{-
Grammar for logs

ExecuteM request processing

RequestRecord ::=
    NodeRequest
    (AbortMarker RequestTime[SimplifyM])*
    (RequestTime[SimplifyM])*
    RequestTime[ExecuteM]

Other requests:
RequestRecord ::=
    NodeRequest RequestTime[tipe]

-}

data RequestRecord = RequestRecord
    { requestId :: RequestId
    , kind :: RequestKind
    , reqTime :: Time -- without internal simplify requests, without kore
    , reqKoreTime :: Time -- without internal simplify requests
    , simpTime :: Time -- sum, without kore
    , simpKoreTime :: Time -- sum
    , simpCount :: Int -- final simplifications only
    , abortCount :: Int
    }
    deriving (Eq, Show)

-- turn [lines] (starting with NodeRequest) into a RequestRecord
parseReqRec :: ReadP RequestRecord
parseReqRec = do
    requestId <- getId <$> satisfy isReq
    fallbacks <- many (parseFallback requestId)
    simpls <- many (parseSimpl requestId)
    finalTime <- satisfy $ isTimeFor requestId
    let reqKoreTime = micros $ koreTimeFrom finalTime
        reqTime = micros $ timeFrom finalTime - reqKoreTime
        simpKoreTime = micros $ sum $ map koreTimeFrom (fallbacks <> simpls)
        simpTime = micros $ sum (map timeFrom (fallbacks <> simpls)) - simpKoreTime
    pure RequestRecord
        { requestId
        , kind = rKind finalTime
        , reqTime
        , reqKoreTime
        , simpTime
        , simpKoreTime
        , simpCount = length simpls
        , abortCount = length fallbacks
        }
  where
    parseFallback :: RequestId -> ReadP Line
    parseFallback r = do
        void $ satisfy isAbort
        satisfy $ \l -> rKind l == SimplifyM && isTimeFor r l

    parseSimpl :: RequestId -> ReadP Line
    parseSimpl r = do
        satisfy $ \l -> rKind l == SimplifyM && isTimeFor r l

    isTimeFor :: RequestId -> Line -> Bool
    isTimeFor r l = isTime l && getId l == r

    timeFrom :: Line -> Time
    timeFrom (RequestTime _ _ t _) = t
    timeFrom other = error $ "no time in " <> show other

    koreTimeFrom :: Line -> Time
    koreTimeFrom (RequestTime _ _ _ t) = t
    koreTimeFrom other = error $ "no kore time in " <> show other

    micros :: Time -> Time
    micros t = fromIntegral (truncate $ t * 1e6) / 1e6

getId :: Line -> RequestId
getId (NodeRequest req) = req
getId (RequestTime req _ _ _) = req
getId (AbortMarker req _) = req

rKind :: Line -> RequestKind
rKind (RequestTime _ kind _ _) = kind
rKind (AbortMarker _ _) = ExecuteM

isReq, isTime, isAbort :: Line -> Bool
isReq NodeRequest{} = True
isReq _other = False
isTime RequestTime{} = True
isTime _other = False
isAbort AbortMarker{} = True
isAbort _other = False

-----------------------------------
-- helpers

-- | split the list whenever the 'sep' predicate yields 'True'. The
-- separator is added to the "back" part (i.e. will be first in the
-- next result, and may be the only element in a result).
splitOn :: Eq a => (a -> Bool) -> [a] -> [[a]]
splitOn sep ls
    | null ls = []
    | (l : ls') <- ls =
        let (front, back) = break sep ls'
         in (l : front) : splitOn sep back

-- | split the list whenever the 'sep' predicate yields
-- 'True'. Identified 'sep' separators are added to the "front" and
-- may be repeated.
splitAfter :: Eq a => (a -> Bool) -> [a] -> [[a]]
splitAfter sep = takeWhile (not . null) . fst . unzip . tail . iterate go . (undefined,)
    where
      -- go :: ([a], [a]) -> ([a], [a])
      go (_, []) = ([], [])
      go (_, xs) =
          let (front, back) = break sep xs
              (seps, rest) = break (not . sep) back
           in (front <> seps, rest)


-- Table of space-separated request record rows with a header
asTable :: [RequestRecord] -> ByteString
asTable = BS.unlines . (header :) . map asRow
  where
    header =
        "Request              Requestkind   ex-time   ex-kore simp-time simp-kore  simp-cnt abort-cnt"
      -- '23...78901234567890'23...789012'23...7890'23...7890'23...7890'23...7890'23...7890'23...7890

    format =
        "%-19s  %-11s " <> "%9.4f %9.4f %9.4f %9.4f  %8d  %8d"
    asRow rr =
        BS.pack $
            printf
                format
                (BS.unpack rr.requestId)
                (show rr.kind)
                rr.reqTime
                rr.reqKoreTime
                rr.simpTime
                rr.simpKoreTime
                rr.simpCount
                rr.abortCount

instance PrintfArg Time
    where formatArg (Time d) = formatArg d

----------------------------------------
-- modified 'ReadP' code for token type 'Line', see Text.ParserCombinators.ReadP
type ReadL a = [Line] -> [(a, [Line])] -- was ReadS

data P a
    = Get (Line -> P a)
    | Look ([Line] -> P a)
    | Fail
    | Result a (P a)
    | Final [(a, [Line])] -- non-empty
    deriving stock Functor
-- Monad, MonadPlus

instance Applicative P where
  pure x = Result x Fail
  (<*>) = ap

instance MonadPlus P

instance Monad P where
  (Get f)         >>= k = Get (\c -> f c >>= k)
  (Look f)        >>= k = Look (\s -> f s >>= k)
  Fail            >>= _ = Fail
  (Result x p)    >>= k = k x <|> (p >>= k)
  (Final (r:rs)) >>= k = final [ys' | (x,s) <- (r:rs), ys' <- run (k x) s]

instance MonadFail P where
  fail _ = Fail

instance Alternative P where
  empty = Fail

  -- most common case: two gets are combined
  Get f1     <|> Get f2     = Get (\c -> f1 c <|> f2 c)
  -- results are delivered as soon as possible
  Result x p <|> q          = Result x (p <|> q)
  p          <|> Result x q = Result x (p <|> q)
  -- fail disappears
  Fail       <|> p          = p
  p          <|> Fail       = p
  -- two finals are combined
  -- final + look becomes one look and one final (=optimization)
  -- final + sthg else becomes one look and one final
  Final r       <|> Final t = Final (r <> t)
  Final (r:rs) <|> Look f  = Look (\s -> Final (r:(rs ++ run (f s) s)))
  Final (r:rs) <|> p       = Look (\s -> Final (r:(rs ++ run p s)))
  Look f        <|> Final r = Look (\s -> Final (case run (f s) s of
                                []     -> r
                                (x:xs) -> (x:xs) <> r))
  p             <|> Final r = Look (\s -> Final (case run p s of
                                []     -> r
                                (x:xs) -> (x:xs) <> r))
  -- two looks are combined (=optimization)
  -- look + sthg else floats upwards
  Look f     <|> Look g     = Look (\s -> f s <|> g s)
  Look f     <|> p          = Look (\s -> f s <|> p)
  p          <|> Look f     = Look (\s -> p <|> f s)


-- Operations over P

final :: [(a,[Line])] -> P a
final []     = Fail
final (r:rs) = Final (r:rs)

run :: P a -> ReadL a
run (Get f)         (c:s) = run (f c) s
run (Look f)        s     = run (f s) s
run (Result x p)    s     = (x,s) : run p s
run (Final (r:rs))  _     = (r:rs)
run _               _     = []

-- | Running the parser:
parseWith :: Show a => ReadP a -> [Line] -> Either String a
parseWith (R f) input =
    case filter (null . snd) $ run (f return) input of
        [] -> Left $ "Parse failed for " <> show input
        [(result, [])] -> Right result
        more -> Left $ "Multiple results: " <> show more

-- The ReadP type

newtype ReadP a = R (forall b . (a -> P b) -> P b)

instance Functor ReadP where
  fmap h (R f) = R (\k -> f (k . h))

instance Applicative ReadP where
    pure x = R (\k -> k x)
    (<*>) = ap
    -- liftA2 = liftM2

instance Monad ReadP where
  R m >>= f = R (\k -> m (\a -> let R m' = f a in m' k))

instance MonadFail ReadP where
  fail _    = R (\_ -> Fail)

instance Alternative ReadP where
  empty = pfail
  (<|>) = (+++)

instance MonadPlus ReadP

-- Operations over ReadP

get :: ReadP Line
-- ^ Consumes and returns the next character.
--   Fails if there is no input left.
get = R Get

look :: ReadP [Line]
-- ^ Look-ahead: returns the part of the input that is left, without
--   consuming it.
look = R Look

pfail :: ReadP a
-- ^ Always fails.
pfail = R (\_ -> Fail)

(+++) :: ReadP a -> ReadP a -> ReadP a
-- ^ Symmetric choice.
R f1 +++ R f2 = R (\k -> f1 k <|> f2 k)

(<++) :: ReadP a -> ReadP a -> ReadP a
-- ^ Local, exclusive, left-biased choice: If left parser
--   locally produces any result at all, then right parser is
--   not used.
R f0 <++ q =
    do s <- look
       probe (f0 return) s 0
  where
    probe (Get f)        (c:s) n = probe (f c) s (n + 1)
    probe (Look f)       s     n = probe (f s) s n
    probe p@(Result _ _) _     n = discard n >> R (p >>=)
    probe (Final r)      _     _ = R (Final r >>=)
    probe _              _     _ = q

    discard 0 = return ()
    discard n = get >> discard (n - 1)

gather :: ReadP a -> ReadP ([Line], a)
-- ^ Transforms a parser into one that does the same, but
--   in addition returns the exact characters read.
--   IMPORTANT NOTE: 'gather' gives a runtime error if its first argument
--   is built using any occurrences of readS_to_P.
gather (R m)
  = R (\k -> gath id (m (\a -> return (\s -> k (s,a)))))
  where
    gath :: ([Line] -> [Line]) -> P ([Line] -> P b) -> P b
    gath l (Get f)      = Get (\c -> gath (l . (c:)) (f c))
    gath _ Fail         = Fail
    gath l (Look f)     = Look (\s -> gath l (f s))
    gath l (Result k p) = k (l []) <|> gath l p
    gath _ (Final _)    = errorWithoutStackTrace "do not use readS_to_P in gather!"

---------------------
-- Derived operations

satisfy :: (Line -> Bool) -> ReadP Line
-- ^ Consumes and returns the next token, if it satisfies the
--   specified predicate.
satisfy p = do c <- get; if p c then return c else pfail

eof :: ReadP ()
-- ^ Succeeds iff we are at the end of input
eof = do { s <- look
         ; if null s then return ()
                     else pfail }


-- or just use Control.Applicative.many?
manyL :: ReadP a -> ReadP [a]
-- ^ Parses zero or more occurrences of the given parser.
manyL p = return [] +++ many1 p

many1 :: ReadP a -> ReadP [a]
-- ^ Parses one or more occurrences of the given parser.
many1 p = liftM2 (:) p (manyL p)
