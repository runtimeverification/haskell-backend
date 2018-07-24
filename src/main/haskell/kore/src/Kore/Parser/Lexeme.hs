{-|
Module      : Kore.Parser.Lexeme
Description : Lexical unit definitions for Kore and simple ways of composing
              parsers. Meant for internal use only.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX

Conventions used:

1. In various cases we distinguish between @object-@ and @meta-@ versions of an
   element. For this we parametrize the element's type with an @a@ and we
   provide an element of type @a@ to the parser, usually called @x@.

2. The meta versions are identified by the presence of @#@ characters at
   the start of the element.

3. All parsers consume the whitespace after the parsed element and expect no
   whitespace before.
-}
module Kore.Parser.Lexeme
    ( colonParser
    , commaParser
    , curlyPairParser
    , curlyPairRemainderParser
    , idParser
    , openCurlyBraceParser
    , inCurlyBracesParser
    , inCurlyBracesRemainderParser
    , inParenthesesParser
    , inSquareBracketsParser
    , keywordBasedParsers
    , metaSortConverter
    , mlLexemeParser
    , moduleNameParser
    , parenPairParser
    , skipWhitespace
    , stringLiteralParser
    , charLiteralParser
    ) where

import Kore.Parser.LexemeImpl
