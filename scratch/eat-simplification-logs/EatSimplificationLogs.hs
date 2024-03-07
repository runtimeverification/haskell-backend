{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad.Trans.Except
import Data.Bifunctor (first, second)
import Data.ByteString.Char8 (ByteString)
import Data.ByteString.Char8 qualified as BS
import Data.Map qualified as Map
import Data.Maybe (fromMaybe, listToMaybe, mapMaybe)
import Text.Regex.Base
import Text.Regex.PCRE

import System.Environment

main :: IO ()
main = do
    args <- getArgs
    contents <- case args of
                    [] -> BS.getContents
                    [file] -> BS.readFile file
    let result =
            either BS.pack (printTree . filterItems (not . isFail))
            . runExcept
            . parse
            . logItems
            . tokenise
            $ contents
    BS.putStrLn result

---------------------------------------- Log Tokeniser
-- going line by line, classify the lines as follows
data Token
    = SeparatorT -- ^kore-rpc: [<number>]...
    | ApplyEqT Location -- ^   applying equation at ...
    | ApplyOKT -- ^   equation is applicable
    | ApplyFailedT -- ^   equation is not applicable
    | AppliedT Location
    | ContextT -- ^Context:
    | LinesT ByteString -- ^ anything other than that: Terms or contexts
  deriving (Eq, Show)

mergeLines :: [Token] -> [Token]
mergeLines = \case
    [] -> []
    (LinesT l1 : rest) -> collect [l1] rest
    (other : rest) -> other : mergeLines rest
  where
    collect acc = \case
        (LinesT next : rest) -> collect (next : acc) rest
        other -> LinesT (BS.unlines $ reverse acc) : mergeLines other

tokenise :: ByteString -> [Token]
tokenise = mergeLines . map classifyLine . BS.lines

classifyLine :: ByteString -> Token
classifyLine bs = fromMaybe (LinesT bs) $ listToMaybe $ mapMaybe (uncurry try) classes
    where
        try :: Regex -> (ByteString -> Token) -> Maybe Token
        try rex f = case matchM rex bs of
                        Nothing ->
                            Nothing
                        Just result@(prefix, matched, suffix, groups)
                            | BS.null prefix
                            , BS.null suffix
                            , matched == bs ->
                                Just $ f (head groups)
                            | otherwise ->
                                error $ "Weird match: " <> show result

        classes = map (first makeRegex)
            [ ("^kore-rpc: \\[[0-9]*\\] .*", const SeparatorT)
            , ("^    applying equation at (.*) to term:", ApplyEqT)
            , ("^    equation is applicable", const ApplyOKT)
            , ("^    equation is not applicable:", const ApplyFailedT)
            , ("^    applied equation at (.*) with result:", AppliedT)
            , ("^Context:" :: ByteString, const ContextT)
            ]

------------------------------------ grouping by separator

data LogItem
    = ApplyEqI Location Term Context
    | ApplyOKI Context
    | ApplyFailedI ByteString Context
    | AppliedI Location Term Context
    | IrrelevantI [Token]
    deriving (Eq, Show)

isIrrelevant IrrelevantI{} = True
isIrrelevant _ = False

logItems :: [Token] -> [LogItem]
logItems = \case
    [] -> []
    (SeparatorT : rest) -> logItems rest
    (ApplyEqT loc : LinesT term : ContextT : LinesT ctx : SeparatorT : rest) ->
        ApplyEqI loc term (BS.lines ctx) : logItems rest
    (ApplyOKT : ContextT : LinesT ctx : SeparatorT : rest) ->
        ApplyOKI (BS.lines ctx) : logItems rest
    (ApplyFailedT : LinesT reason : ContextT : LinesT ctx : SeparatorT : rest) ->
        ApplyFailedI reason (BS.lines ctx) : logItems rest
    (AppliedT loc : LinesT result : ContextT : LinesT ctx : SeparatorT : rest) ->
        AppliedI loc result (BS.lines ctx) : logItems rest
    (AppliedT loc : LinesT result : SeparatorT : rest) -> -- top of stack, no context
        AppliedI loc result [] : logItems rest
    (other : rest) ->
        let isSep SeparatorT{} = True
            isSep _ = False
        in IrrelevantI (other : takeWhile (not . isSep) rest) : logItems (dropWhile (not . isSep) rest)


------------------------------------ classification
type Term = ByteString
type Context = [ByteString]
type Location = ByteString

data TraceItem
    = Applied ApplyRule
    | Failed ApplyFailed
    | Other [LogItem]
    deriving (Eq, Show)

data ApplyRule
    = ApplyRule
        { location :: Location
        , term :: Term
        , context :: Context
        , result :: Term
        , inner :: [TraceItem]
        }
    deriving (Eq, Show)
data ApplyFailed
    = ApplyFailed
        { location :: Location
        , term :: Term
        , reason :: ByteString
        , context :: Context
        , inner :: [TraceItem]
        }
    deriving (Eq, Show)

recognise :: [LogItem] -> Except String (Maybe TraceItem, [LogItem])
recognise = \case
    -- successful rule application
    (ApplyEqI _loc term _ctx :
        ApplyOKI ctx :
        AppliedI location result context :
        rest) ->
            pure (Just $ Applied $ ApplyRule { location, term, context, result, inner = []}, rest)
    -- failed rule application
    (ApplyEqI location term ctx :
        ApplyFailedI reason context :
        rest ) ->
            pure (Just $ Failed $ ApplyFailed {location, term, reason, context, inner = []}, rest)
    -- recursive evaluation
    (app@ApplyEqI{} : innerTs@(ApplyEqI{} : _)) -> do
            (inner, rest') <- run innerTs
            (current, rest) <- recognise (app : rest')
            result <-
                    case current of -- additional fields for disambiguation
                        Just (Failed a) -> pure $ Failed a { reason = a.reason , inner }
                        Just (Applied a) -> pure $ Applied a { result = a.result, inner }
                        Just (Other x) -> pure $ Other x
                        Nothing -> throwE $ "Unable to parse" <> show (app : take 5 rest')
            pure (Just result, rest)
    [app@ApplyEqI{}] ->
        pure (Just $ Other [app], [])
    (ApplyEqI loc _ _ : otherStuff) ->
                  throwE $ "Apply without expected sequent: " <> unlines (map (take 80 . show) $ take 6 otherStuff)
    -- not starting with an ApplyEqT: stop (might be recursion case)
    other -> pure (Nothing, other)

run ::
    [LogItem] ->
    Except String ([TraceItem], [LogItem])
run input = do
    (mbHead, rest) <- recognise input
    case mbHead of
        Nothing ->
            pure ([], rest)
        Just headItem -> do
            (items, rest') <- run rest
            pure (headItem : items, rest')

parse :: [LogItem] -> Except String [TraceItem]
parse input =
    go $ filter (not . isIrrelevant) input
  where
    go [] = pure []
    go (hd:rest) =
        run (hd:rest) >>= \case
            ([], _) -> (Other [hd] :) <$> go rest
            (result, rest)
                | null rest -> pure result
                | otherwise -> pure $ result <> [Other rest]

------------------------------------------------------------
-- Manipulating the results

isFail :: TraceItem -> Bool
isFail Failed{} = True
isFail _ = False

filterItems :: (TraceItem -> Bool) -> [TraceItem] -> [TraceItem]
filterItems p = mapMaybe $ \case
    item | not (p item) -> Nothing
    Applied applyRule ->
        Just . Applied $ applyRule { result = applyRule.result, inner = filterItems p applyRule.inner }
    Failed applyFailed ->
        Just . Failed $ applyFailed { reason = applyFailed.reason, inner = filterItems p applyFailed.inner }
    other@Other{} -> Just other

-- output
printTree :: [TraceItem] -> ByteString
printTree = BS.intercalate "----\n" . map (printItem . cleanTerms)

printItem :: TraceItem -> ByteString
printItem = \case
    Applied applyRule ->
        BS.unlines $
            [applyRule.location, applyRule.term, "  evaluated to:", applyRule.result]
                <> if null applyRule.inner then [] else "with recursive simplifications: ": [indent 2 (printTree applyRule.inner)]
    Failed applyFailed ->
        BS.unlines $
            [applyFailed.location, applyFailed.term, "  failed to apply: " <> applyFailed.reason]
                <> if null applyFailed.inner then [] else "Considered recursive simplifications:": [indent 2 (printTree applyFailed.inner)]
    Other ls ->
        BS.unlines $ map ("Other log item: " <>) $ map (BS.pack . show) ls
  where
    indent :: Int -> ByteString -> ByteString
    indent n = BS.unlines . map (BS.pack (replicate (n - 1) ' ' <> "|") <>) . BS.lines

-- | removes all comment cruft and (resulting) empty lines
cleanTerm :: Term -> Term
cleanTerm = BS.unlines . filter notEmpty . map go . BS.lines
  where
    notEmpty :: ByteString -> Bool
    notEmpty = not . match emptyLine

    go :: ByteString -> ByteString
    go = tweakIdentifiers . removeComments

emptyLine :: Regex
emptyLine = makeRegex ("^ *$" :: ByteString)

removeComments, tweakIdentifiers :: ByteString -> ByteString
removeComments bs
    | BS.null commentStart = bs
    | BS.null suffix = prefix
    | otherwise = prefix <> removeComments (BS.drop 2 suffix)
  where
    (prefix, commentStart) = BS.breakSubstring "/*" bs
    (_comment, suffix) = BS.breakSubstring "*/" $ BS.drop 2 commentStart

tweakIdentifiers = go
  where
    go bs = case matchM identifier bs of
                Nothing -> bs
                Just (prefix, identifier, suffix, _ :: [ByteString]) ->
                    prefix <> unescape identifier <> go suffix
      where
        unescape str
            | BS.null escaped = str
            | otherwise = prefix <> unescape' (BS.tail escaped)
                where (prefix, escaped) = BS.break (=='\'') str

                      unescape' s
                          | BS.null s = error $ "tweakIdentifiers: Bad escape quote nesting in " <> show str
                          | '\'' <- BS.head s =
                              unescape $ BS.tail s
                          | otherwise =
                              replace hd <> unescape' rest
                        where
                          (hd, rest) = BS.splitAt 4 s

        replace x =
            fromMaybe (error $ "Bad escape code: " <> show x <> " in " <> show bs) $ Map.lookup x decodeMap

decodeMap :: Map.Map ByteString ByteString
decodeMap =
    Map.fromList
        [ ("Spce", " ")
        , ("Bang", "!")
        , ("Quot", "\"")
        , ("Hash", "#")
        , ("Dolr", "$")
        , ("Perc", "%")
        , ("And-", "&")
        , ("Apos", "'")
        , ("LPar", "(")
        , ("RPar", ")")
        , ("Star", "*")
        , ("Plus", "+")
        , ("Comm", ",")
        , ("Hyph", "-")
        , ("Stop", ".")
        , ("Slsh", "/")
        , ("Coln", ":")
        , ("SCln", ";")
        , ("-LT-", "<")
        , ("Eqls", "=")
        , ("-GT-", ">")
        , ("Ques", "?")
        , ("-AT-", "@")
        , ("LSqB", "[")
        , ("RSqB", "]")
        , ("Bash", "\\")
        , ("Xor-", "^")
        , ("Unds", "_")
        , ("BQuo", "`")
        , ("LBra", "{")
        , ("Pipe", "|")
        , ("RBra", "}")
        , ("Tild", "~")
        ]

identifier :: Regex
identifier = makeRegex ("[A-Za-z0-9'-]+" :: ByteString)


cleanTerms :: TraceItem -> TraceItem
cleanTerms (Applied apply) =
    Applied apply { term = cleanTerm apply.term, result = cleanTerm apply.result, inner = map cleanTerms apply.inner }
cleanTerms (Failed failure) =
    Failed failure { term = cleanTerm failure.term, reason = failure.reason, inner = map cleanTerms failure.inner }
cleanTerms (Other bs) = Other bs
