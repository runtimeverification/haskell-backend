{
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-missing-deriving-strategies #-}
{-# OPTIONS -funbox-strict-fields #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause

Lexical analyzer for parser of KORE text. At a high level, converts a string
into a sequence of whitespace-insensitive tokens to be interpreted by the
parser.

-}

module Kore.Parser.Lexer (
    Alex(..),
    AlexInput(..),
    AlexPosn(..),
    AlexReturn(..),
    AlexState(..),
    Token(..),
    TokenClass(..),
    alexError,
    alexScanUser,
    getIdentName,
    getTokenClass,
) where

import Control.Applicative as App (Applicative (..))
import Control.Monad (
    liftM,
    when,
 )
import Data.ByteString qualified as ByteString
import Data.ByteString.Internal qualified as ByteString hiding (ByteString)
import Data.ByteString.Unsafe qualified as ByteString
import Data.Char (
    chr,
    digitToInt,
    generalCategory,
    GeneralCategory(..),
    isPrint,
 )
import Data.List qualified as List
import Data.Text (
    Text,
 )
import Data.Text qualified as Text
import Data.Text.Encoding
import Data.Word (Word8)
import Numeric
import Prelude

}

@ident = [a-zA-Z][a-zA-Z0-9'\-]*
@setIdent = [\@][a-zA-Z][a-zA-Z0-9'\-]*

tokens :-

  $white+                              ;
  module                               { tok        TokenModule }
  endmodule                            { tok        TokenEndModule }
  import                               { tok        TokenImport }
  sort                                 { tok        TokenSort }
  symbol                               { tok        TokenSymbol }
  where                                { tok        TokenWhere }
  alias                                { tok        TokenAlias }
  axiom                                { tok        TokenAxiom }
  claim                                { tok        TokenClaim }
  hooked[\-]sort                       { tok        TokenHookedSort }
  hooked[\-]symbol                     { tok        TokenHookedSymbol }
  [\:][\=]                             { tok        TokenColonEqual }
  [\:]                                 { tok        TokenColon }
  [\{]                                 { tok        TokenLeftBrace }
  [\}]                                 { tok        TokenRightBrace }
  [\[]                                 { tok        TokenLeftBracket }
  [\]]                                 { tok        TokenRightBracket }
  [\(]                                 { tok        TokenLeftParen }
  [\)]                                 { tok        TokenRightParen }
  [\,]                                 { tok        TokenComma }
  [\\]top                              { tok        TokenTop }
  [\\]bottom                           { tok        TokenBottom }
  [\\]not                              { tok        TokenNot }
  [\\]and                              { tok        TokenAnd }
  [\\]or                               { tok        TokenOr }
  [\\]implies                          { tok        TokenImplies }
  [\\]iff                              { tok        TokenIff }
  [\\]exists                           { tok        TokenExists }
  [\\]forall                           { tok        TokenForall }
  [\\]mu                               { tok        TokenMu }
  [\\]nu                               { tok        TokenNu }
  [\\]ceil                             { tok        TokenCeil }
  [\\]floor                            { tok        TokenFloor }
  [\\]equals                           { tok        TokenEquals }
  [\\]in                               { tok        TokenIn }
  [\\]next                             { tok        TokenNext }
  [\\]rewrites                         { tok        TokenRewrites }
  [\\]dv                               { tok        TokenDomainValue }
  [\\]left[\-]assoc                    { tok        TokenLeftAssoc }
  [\\]right[\-]assoc                   { tok        TokenRightAssoc }
  [\\]?@ident                          { tok_ident TokenIdent }
  [\\]?@setIdent                       { tok_ident TokenSetIdent }
  [\"](
    ([^\"\n\r\\])
  | ([\\][nrtf\"\\])
  | ([\\][x][0-9a-fA-F]{2})
  | ([\\][u][0-9a-fA-F]{4})
  | ([\\][U][0-9a-fA-F]{8})
  )*[\"]                               { tok_string }
  [\/][\/][^\n\r]*                     ;
  [\/][\*](([^\*]|[\n])|(\*+([^\*\/]|[\n])))*\*+\/ ;

{

-- Token helpers
tok' :: (Text -> TokenClass) -> AlexInput -> Int -> Alex Token
tok' f AlexInput{alexPosn, alexStr} len = do
  return $ Token alexPosn (f (decodeUtf8 (ByteString.take len alexStr)))

-- | Lexer action to construct a token with a particular constant TokenClass
tok :: TokenClass -> AlexInput -> Int -> Alex Token
tok x = tok' (const x)

{- | Lexer action to construct an identifier token with a particular TokenClass
using the current text of the token as its Text argument.
-}
tok_ident :: (Text -> TokenClass) -> AlexInput -> Int -> Alex Token
tok_ident x = tok' (\s -> x s)

{- | Lexer action to construct a string token with the TokenString TokenClass.
The string is unescaped prior to its Text argument being placed inside the
token.
-}
tok_string :: AlexInput -> Int -> Alex Token
tok_string AlexInput{alexPosn=p@(AlexPn fp _ line column), alexStr} len = do
  let text = decodeUtf8 (ByteString.take len alexStr)
      unescaped = unescape text in case unescaped of
                                        Left str -> alexError fp line column str
                                        Right t -> return $ Token p (TokenString t)
   
-- | Data type for Tokens. Contains filename, location info, and TokenClass
data Token = Token AlexPosn TokenClass
  deriving stock (Eq)
  deriving stock (Show)

{- | Get the Text argument of a Token whose TokenClass contains such an 
argument
-}
getIdentName :: Token -> Text
getIdentName (Token _ (TokenIdent t)) = t
getIdentName (Token _ (TokenSetIdent t)) = t
getIdentName _ = error "getIdentName can only be called on TokenIdent or TokenSetIdent"


-- | Get the TokenClass of a Token
getTokenClass :: Token -> TokenClass
getTokenClass (Token _ cls) = cls

{- | Data type for the raw lexical data of a Token. Essentially an enumeration
specifying which token a particular Token represents. Additionally contains the
semantic data associated with identifier and string tokens.
-}
data TokenClass
  = TokenModule
  | TokenEndModule
  | TokenImport
  | TokenSort
  | TokenSymbol
  | TokenWhere
  | TokenAlias
  | TokenAxiom
  | TokenClaim
  | TokenHookedSort
  | TokenHookedSymbol
  | TokenColonEqual
  | TokenColon
  | TokenLeftBrace
  | TokenRightBrace
  | TokenLeftBracket
  | TokenRightBracket
  | TokenLeftParen
  | TokenRightParen
  | TokenComma
  | TokenTop
  | TokenBottom
  | TokenNot
  | TokenAnd
  | TokenOr
  | TokenImplies
  | TokenIff
  | TokenExists
  | TokenForall
  | TokenMu
  | TokenNu
  | TokenCeil
  | TokenFloor
  | TokenEquals
  | TokenIn
  | TokenNext
  | TokenRewrites
  | TokenDomainValue
  | TokenLeftAssoc
  | TokenRightAssoc
  | TokenIdent Text
  | TokenSetIdent Text
  | TokenString Text
  | TokenEOF
  deriving stock (Eq, Show)

-- -----------------------------------------------------------------------------
-- Alex wrapper code.
--
-- Taken and modified from public domain code that is part of Alex:
-- https://github.com/haskell/alex/blob/3.2.6/templates/wrappers.hs
--
-- Unlike the code in LexerWrapper.hs, this code must live in the same module
-- as the scanner itself, so it was moved from that file to this one.


alexScanUser :: () -> AlexInput -> Int -> AlexReturn (AlexInput -> Int -> Alex Token)

data AlexInput = AlexInput { alexPosn :: {-# UNPACK #-} !AlexPosn,
                             alexChar :: {-# UNPACK #-} !Char,
                             alexStr :: {-# UNPACK #-} !ByteString.ByteString,
                             alexBytePos :: {-# UNPACK #-} !Int}

data AlexPosn = AlexPn !FilePath !Int !Int !Int
        deriving (Eq,Show)

data AlexState = AlexState {
        alex_pos :: !AlexPosn,  -- position at current input location
        alex_bpos:: !Int,     -- bytes consumed so far
        alex_inp :: ByteString.ByteString,      -- the current input
        alex_chr :: !Char,      -- the character before the input
        alex_scd :: !Int        -- the current startcode
    }

newtype Alex a = Alex { unAlex :: AlexState -> Either String (AlexState, a) }

instance Functor Alex where
  fmap f a = Alex $ \s -> case unAlex a s of
                            Left msg -> Left msg
                            Right (s', a') -> Right (s', f a')
  {-# INLINE fmap #-}

instance Applicative Alex where
  pure a   = Alex $ \s -> Right (s, a)
  fa <*> a = Alex $ \s -> case unAlex fa s of
                            Left msg -> Left msg
                            Right (s', f) -> case unAlex a s' of
                                               Left msg -> Left msg
                                               Right (s'', b) -> Right (s'', f b)
  {-# INLINE (<*>) #-}

instance Monad Alex where
  m >>= k  = Alex $ \s -> case unAlex m s of
                                Left msg -> Left msg
                                Right (s',a) -> unAlex (k a) s'
  {-# INLINE (>>=) #-}

alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte (AlexInput {alexPosn=p,alexStr=cs,alexBytePos=n}) =
    case ByteString.uncons cs of
        Nothing -> Nothing
        Just (c, rest) -> 
          let b = ByteString.w2c c in
            Just (c, AlexInput {
                alexPosn = alexMove p b,
                alexChar = b,
                alexStr =  rest,
                alexBytePos = n+1})

alexMove :: AlexPosn -> Char -> AlexPosn
alexMove (AlexPn fp a l c) '\t' =
    AlexPn fp (a+1) l (c+alex_tab_size-((c-1) `mod` alex_tab_size))
alexMove (AlexPn fp a l _) '\n' = AlexPn fp (a+1) (l+1) 1
alexMove (AlexPn fp a l c) _    = AlexPn fp (a+1) l (c+1)

alexError :: FilePath -> Int -> Int -> String -> Alex a
alexError fp line column msg =
    Alex $ const $ Left $ unwords [header, msg] ++ "\n"
    where
        header = List.intercalate ":" [fp, show line, show column] ++ ":"

-- End Alex wrapper code.

{- | Convert the textual representation of a string token into its semantic
value as a Text. Returns Left with an error message if it fails, otherwise
Right.
-}
unescape :: Text -> Either String Text
unescape t =
  let dropQuotes str = Text.take (Text.length str - 2) . Text.drop 1 $ str
      escape rest c = either Left (\s -> Right (c : s)) $ go rest
      validate rest c
          | c > 0x10ffff = Left ("code point " ++ show c ++ " outside range of Unicode")
          | generalCategory (chr c) == Surrogate 
              = Left ("surrogate character " ++ show (chr c) ++ " in string literal")
          | otherwise = escape rest $ chr c
      go [] = Right []
      go ('\\' : 'n' : rest) = escape rest '\n'
      go ('\\' : 'r' : rest) = escape rest '\r'
      go ('\\' : 't' : rest) = escape rest '\t'
      go ('\\' : 'f' : rest) = escape rest '\f'
      go ('\\' : '\\' : rest) = escape rest '\\'
      go ('\\' : '"' : rest) = escape rest '"'
      go ('\\' : pre : rest0)
          | Just size <- lookup pre $ zip "xuU" [2,4,8]
          , (body, rest) <- splitAt size rest0
          , length body == size
          = runReadS Numeric.readHex body
              >>= validate rest
        where
            runReadS reader str = case reader str of
                [(num, "")] -> pure num
                _other -> Left "invalid hex literal"
      go ('\\' : _) = error "should be unreachable"
      go (c : rest)
          | isPrint c = escape rest c
          | otherwise 
              = Left ("non-printable character " ++ show c ++ " in string literal")
  in either Left (Right . Text.pack) $ go $ Text.unpack $ dropQuotes t
}
