{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-missing-signatures #-}
{-# LANGUAGE CPP,MagicHash #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-missing-deriving-strategies #-}
{-# OPTIONS -funbox-strict-fields #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}

module Kore.Parser.LexerWrapper (
    alexMonadScan,
    alexScanTokens,
    runAlex,
) where
-- -----------------------------------------------------------------------------
-- Alex wrapper code.
--
-- Taken and modified from public domain code that is part of Alex: 
-- https://github.com/haskell/alex/blob/3.2.6/templates/wrappers.hs

import Control.Applicative as App (Applicative (..))
import Data.Word (Word8)
import qualified Data.Char
import qualified Data.ByteString          as ByteString
import qualified Data.ByteString.Internal as ByteString hiding (ByteString)
import qualified Data.ByteString.Unsafe   as ByteString
import Data.Int
import Kore.Parser.Lexer
import Prelude.Kore

type Byte = Word8

-- -----------------------------------------------------------------------------
-- The input type

ignorePendingBytes :: AlexInput -> AlexInput
ignorePendingBytes i = i   -- no pending bytes when lexing bytestrings

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar = alexChar

-- -----------------------------------------------------------------------------
-- Token positions

-- `Posn' records the location of a token in the input text.  It has three
-- fields: the address (number of chacaters preceding the token), line number
-- and column of a token within the file. `start_pos' gives the position of the
-- start of the file and `eof_pos' a standard encoding for the end of file.
-- `move_pos' calculates the new position after traversing a given character,
-- assuming the usual eight character tab stops.

alexStartPos :: FilePath -> AlexPosn
alexStartPos fp = AlexPn fp 0 1 1

-- -----------------------------------------------------------------------------
-- Monad (default and with ByteString input)

-- Compile with -funbox-strict-fields for best results!

runAlex :: FilePath -> ByteString.ByteString -> Alex a -> Either String a
runAlex fp input__ (Alex f)
   = case f (AlexState {alex_bpos = 0,
                        alex_pos = alexStartPos fp,
                        alex_inp = input__,
                        alex_chr = '\n',
                        alex_scd = 0}) of Left msg -> Left msg
                                          Right ( _, a ) -> Right a
alexGetInput :: Alex AlexInput
alexGetInput
 = Alex $ \s@AlexState{alex_pos=pos,alex_bpos=bpos,alex_chr=c,alex_inp=inp__} ->
        Right (s, AlexInput{alexPosn=pos,alexChar=c,alexStr=inp__,alexBytePos=bpos})

alexSetInput :: AlexInput -> Alex ()
alexSetInput AlexInput{alexPosn=pos,alexChar=c,alexStr=inp__,alexBytePos=bpos}
 = Alex $ \s -> case s{alex_pos=pos,
                       alex_bpos=bpos,
                       alex_chr=c,
                       alex_inp=inp__} of
                  state__@(AlexState{}) -> Right (state__, ())

alexGetStartCode :: Alex Int
alexGetStartCode = Alex $ \s@AlexState{alex_scd=sc} -> Right (s, sc)

alexSetStartCode :: Int -> Alex ()
alexSetStartCode sc = Alex $ \s -> Right (s{alex_scd=sc}, ())

alexEOF :: Alex Token
alexEOF = do
  AlexInput{alexPosn=p} <- alexGetInput
  return $ Token p TokenEOF

alexMonadScan = do
  inp__@AlexInput{alexBytePos=n} <- alexGetInput
  sc <- alexGetStartCode
  case alexScanUser () inp__ sc of
    AlexEOF -> alexEOF
    AlexError(AlexInput{alexPosn=(AlexPn fp _ line column),alexStr=s}) -> alexError fp line column (if s == "" then "unexpected end of input" else "unexpected character " ++ show (ByteString.w2c $ ByteString.head s))
    AlexSkip  inp__' _len -> do
        alexSetInput inp__'
        alexMonadScan
    AlexToken inp__'@AlexInput{alexBytePos=n'} _ action -> let len = n'-n in do
        alexSetInput inp__'
        action (ignorePendingBytes inp__) len

-- -----------------------------------------------------------------------------
-- Useful token actions

type AlexAction result = AlexInput -> Int64 -> Alex result

-- just ignore this token and scan another one
-- skip :: AlexAction result
skip _input _len = alexMonadScan

-- ignore this token, but set the start code to a new value
-- begin :: Int -> AlexAction result
begin code _input _len = do alexSetStartCode code; alexMonadScan

-- perform an action for this token, and set the start code to a new value
andBegin :: AlexAction result -> Int -> AlexAction result
(action `andBegin` code) input__ len = do
  alexSetStartCode code
  action input__ len

token :: (AlexInput -> Int64 -> token) -> AlexAction token
token t input__ len = return (t input__ len)

-- -----------------------------------------------------------------------------
-- Basic wrapper, ByteString version

-- | Monad that repeats an operation until a boolean predicate returns True.
whileM :: Monad m => (a -> Bool) -> m a -> m [a]
whileM p f = go
  where go = do
          x <- f
          if p x
                then do
                        xs <- go
                        return (x : xs)
                else return []

-- | Returns True if the specified Token is not the EOF token.
isNotEOF :: Token -> Bool
isNotEOF (Token _ TokenEOF) = False
isNotEOF _ = True

{- | Helper function to perform lexical analysis without parsing. Useful only
for testing and debuggging.
-}
alexScanTokens :: FilePath -> ByteString.ByteString -> Either String [Token]
alexScanTokens fp input = runAlex fp input (whileM isNotEOF alexMonadScan)
