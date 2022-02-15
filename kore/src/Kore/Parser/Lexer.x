{
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-missing-deriving-strategies #-}
{-# OPTIONS -funbox-strict-fields #-}
{-# LANGUAGE NoStrict #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause

Lexical analyzer for parser of KORE text. At a high level, converts a string
into a sequence of whitespace-insensitive tokens to be interpreted by the
parser.

--}

module Kore.Parser.Lexer (
    Alex(..),
    AlexPosn(..),
    AlexState(..),
    Token(..),
    TokenClass(..),
    alexError,
    alexErrorPretty,
    alexMonadScanPath,
    alexScanTokens,
    getTokenBody,
    getTokenClass,
    runAlexPath,
) where

import Control.Monad (
    liftM,
    when,
 )
import qualified Data.ByteString.Lazy.Char8 as B
import Data.Char (
    chr,
    digitToInt,
    generalCategory,
    GeneralCategory(..),
    isPrint,
 )
import Data.Text (
    Text,
 )
import qualified Data.Text as Text
import Data.Text.Encoding
import Prelude

}

%wrapper "monadUserState-bytestring"

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
tok' f (p, _, input, _) len = do
  fp <- getFilePath
  return $ Token fp p (f (decodeUtf8 (B.toStrict (B.take (fromIntegral len) input))))

-- | Lexer action to construct a token with a particular constant TokenClass
tok x = tok' (const x)

{- | Lexer action to construct an identifier token with a particular TokenClass
using the current text of the token as its Text argument.
-}
tok_ident x = tok' (\s -> x s)

{- | Lexer action to construct a string token with the TokenString TokenClass.
The string is unescaped prior to its Text argument being placed inside the
token.
-}
tok_string (p@(AlexPn _ line column), _, input, _) len = do
  fp <- getFilePath
  let text = decodeUtf8 (B.toStrict (B.take (fromIntegral len) input))
      unescaped = unescape text in case unescaped of
                                        Left str -> alexErrorPretty line column str
                                        Right t -> return $ Token fp p (TokenString t)
   
-- | Data type for Tokens. Contains filename, location info, and TokenClass
data Token = Token FilePath AlexPosn TokenClass
  deriving stock (Eq)
  deriving stock (Show)

{- | Get the Text argument of a Token whose TokenClass contains such an 
argument
-}
getTokenBody :: Token -> Text
getTokenBody (Token _ _ (TokenIdent t)) = t
getTokenBody (Token _ _ (TokenSetIdent t)) = t
getTokenBody (Token _ _ (TokenString t)) = t
getTokenBody _ = error "getTokenBody can only be called on tokens which contain a Text field"


-- | Get the TokenClass of a Token
getTokenClass :: Token -> TokenClass
getTokenClass (Token _ _ cls) = cls

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

-- | Monad that returns an EOF Token
alexEOF :: Alex Token
alexEOF = do
  fp <- getFilePath
  (p, _, _, _) <- alexGetInput
  return $ Token fp p TokenEOF

-- | User state of Alex Monad. Contains file path of file being analyzed.
data AlexUserState = AlexUserState { filePath :: FilePath }

{- | Initial state of Alex Monad. Should be overridden with setFilePath if 
possible.
-}
alexInitUserState = AlexUserState "<unknown>"

-- | Returns the user state of the Alex Monad.
alexGetUserState :: Alex AlexUserState
alexGetUserState = Alex $ \s@AlexState{alex_ust=ust} -> Right (s,ust)

-- | Sets the user state of the Alex Monad.
alexSetUserState :: AlexUserState -> Alex ()
alexSetUserState ss = Alex $ \s -> Right (s{alex_ust=ss}, ())

-- | Gets the current file path within the Alex Monad.
getFilePath :: Alex FilePath
getFilePath = liftM filePath alexGetUserState

-- | Sets the current file path within the Alex Monad.
setFilePath :: FilePath -> Alex ()
setFilePath = alexSetUserState . AlexUserState

{- | Returns a lexical error with the specified line, column, and error
message.
-}
alexErrorPretty :: Int -> Int -> String -> Alex a
alexErrorPretty line column msg = do
    fp <- getFilePath
    alexError (fp ++ ":" ++ show line ++ ":" ++ show column ++ ": " ++ msg ++ "\n")

-- | Replacement for alexMonadScan which also processes a FilePath.
alexMonadScanPath = do
  input@(_,_,_,n) <- alexGetInput
  sc <- alexGetStartCode
  case alexScan input sc of
    AlexEOF -> alexEOF
    AlexError ((AlexPn _ line column),_,s,_) -> let nextChar = B.unpack $ B.take 1 s in alexErrorPretty line column (if nextChar == "" then "unexpected end of input" else "unexpected character '" ++ nextChar ++ "'")
    AlexSkip  input' _ -> do
        alexSetInput input'
        alexMonadScanPath
    AlexToken input'@(_,_,_,n') _ action -> let len = n'-n in do
        alexSetInput input'
        action (ignorePendingBytes input) len

-- | Replacement for runAlex which also processes a FilePath.
runAlexPath :: Alex a -> FilePath -> B.ByteString -> Either String a
runAlexPath a fp input = runAlex input (setFilePath fp >> a)

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
isNotEOF (Token _ _ TokenEOF) = False
isNotEOF _ = True

{- | Helper function to perform lexical analysis without parsing. Useful only
for testing and debuggging.
-}
alexScanTokens :: FilePath -> B.ByteString -> Either String [Token]
alexScanTokens fp input = runAlexPath (whileM isNotEOF alexMonadScanPath) fp input

{- | Convert the textual representation of a string token into its semantic
value as a Text. Returns Left with an error message if it fails, otherwise
Right.
-}
unescape :: Text -> Either String Text
unescape t =
  let drop_quotes str = Text.take (Text.length str - 2) . Text.drop 1 $ str
      escape rest c = either Left (\s -> Right (c : s)) $ go rest
      validate rest c | c >= 0x10ffff = Left ("code point " ++ show c ++ " outside range of Unicode")
                      | generalCategory (chr c) == Surrogate = Left ("surrogate character " ++ show (chr c) ++ " in string literal")
                      | otherwise = escape rest $ chr c
      go [] = Right []
      go ('\\' : 'n' : rest) = escape rest '\n'
      go ('\\' : 'r' : rest) = escape rest '\r'
      go ('\\' : 't' : rest) = escape rest '\t'
      go ('\\' : 'f' : rest) = escape rest '\f'
      go ('\\' : '\\' : rest) = escape rest '\\'
      go ('\\' : '"' : rest) = escape rest '"'
      go ('\\' : 'x' : first : second : rest) = escape rest $ chr (digitToInt first * 16 + digitToInt second)
      go ('\\' : 'u' : first : second : third : fourth : rest) = validate rest $ (((digitToInt first * 16 + digitToInt second) * 16 + digitToInt third) * 16 + digitToInt fourth)
      go ('\\' : 'U' : first : second : third : fourth : fifth : sixth : seventh : eighth : rest) = validate rest $ (((((((digitToInt first * 16 + digitToInt second) * 16 + digitToInt third) * 16 + digitToInt fourth) * 16 + digitToInt fifth) * 16 + digitToInt sixth) * 16 + digitToInt seventh) * 16 + digitToInt eighth)
      go ('\\' : _) = error "should be unreachable"
      go (c : rest) | isPrint c = escape rest c
                    | otherwise = Left ("non-printable character " ++ show c ++ " in string literal")
  in either Left (Right . Text.pack) $ go $ Text.unpack $ drop_quotes t
}
