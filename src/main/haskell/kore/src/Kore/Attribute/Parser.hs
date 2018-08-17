{-|
Module      : Kore.Attribute.Parser
Description : Attribute parsers
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

This module defines attribute parsers and a class 'ParseAttributes' for types
which can be parsed from an attribute list.

This module is intended to be imported qualified or explicitly:

@
  import Kore.Attribute.Parser ( parseAttributes, ParseAttributes (..) )
  import qualified Kore.Attribute.Parser as Attribute
@

-}
module Kore.Attribute.Parser
    ( -- * Parsing attributes
      parseAttributes
    , ParseAttributes (..)
      -- * Parsers
    , Parser
    , ParseError
    , Occurrence (..)
    , AttributeMap
    , runParser
    , withContext
      -- ** Parsing idioms
    , parseAttribute
    , parseKeyAttribute
    , hasKeyAttribute
    , parseStringAttribute
    , assertNoAttribute
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import           Control.Monad
                 ( foldM, when, (>=>) )
import           Control.Monad.Except
                 ( MonadError (catchError, throwError) )
import           Control.Monad.Reader
                 ( MonadReader, ReaderT (runReaderT) )
import qualified Control.Monad.Reader as Reader
import           Data.Default
                 ( Default )
import           Data.Functor
                 ( ($>) )
import           Data.HashMap.Strict
                 ( HashMap )
import qualified Data.HashMap.Strict as HashMap
import           Data.List.NonEmpty
                 ( NonEmpty ((:|)) )
import qualified Data.List.NonEmpty as NonEmpty

import           Kore.AST.Common
                 ( Application (..), Id (..),
                 Pattern (ApplicationPattern, StringLiteralPattern),
                 StringLiteral (..), SymbolOrAlias (..), Variable )
import           Kore.AST.Kore
                 ( CommonKorePattern, pattern KoreMetaPattern,
                 pattern KoreObjectPattern )
import           Kore.AST.MetaOrObject
                 ( Meta, Object )
import           Kore.AST.Sentence
                 ( Attributes (Attributes) )
import           Kore.Error
                 ( Error, koreFail )
import qualified Kore.Error

parseAttributes :: ParseAttributes atts => Attributes -> Either (Error ParseError) atts
parseAttributes = runParser attributesParser

class Default atts => ParseAttributes atts where
    {- | Parse 'Attributes' to produce @atts@.

      See also: 'parseAttributes'

     -}
    attributesParser :: Parser atts

-- | One occurrence of an attribute, represented as a list of its arguments.
newtype Occurrence = Occurrence { getOccurrence :: [CommonKorePattern] }

-- | A map from attribute names to a non-empty list of its 'Occurence's.
type AttributeMap = HashMap String (NonEmpty Occurrence)

data ParseError

{- | Parse 'Attributes' to produce @a@.

  The parser can read the 'AttributeMap' through the 'MonadReader' instance.

  The parser throws and catches errors with 'throwError' and 'catchError' from
  'MonadError'.

 -}
newtype Parser a =
    Parser
    { getParser :: ReaderT AttributeMap (Either (Error ParseError)) a }
  deriving (Applicative, Functor, Monad)

deriving instance MonadError (Error ParseError) Parser

deriving instance MonadReader AttributeMap Parser

instance Alternative Parser where
    empty = koreFail "parse error"
    -- If both actions fail, prefer the first failure.
    (<|>) a b = catchError a (\e -> catchError b (\_ -> throwError e))

{- | Run an attribute 'Parser' with the given list of attributes.
 -}
runParser :: Parser a -> Attributes -> Either (Error ParseError) a
runParser Parser { getParser } (Attributes attrs) = do
    -- attributeMap associates the arguments of an attribute (each time it
    -- occurs) with the name of the attribute
    attributeMap <- foldM recordOccurrence HashMap.empty attrs
    runReaderT getParser attributeMap
  where
    -- | Record one occurrence of an attribute.
    recordOccurrence
        :: AttributeMap
        -- ^ the attributes already recorded
        -> CommonKorePattern
        -- ^ one attribute, which must be an object-level application pattern
        -> Either (Error ParseError) AttributeMap
    recordOccurrence attrMap attr =
        case attr of
            KoreObjectPattern (ApplicationPattern app) ->
                recordApplication attrMap app
            _ -> koreFail "expected object-level application pattern"

    -- | Insert the application arguments into the attribute map,
    -- on top of any argument lists already present.
    recordApplication
        :: AttributeMap
        -> Application Object CommonKorePattern
        -> Either (Error ParseError) AttributeMap
    recordApplication
        attrMap
        Application
            { applicationSymbolOrAlias
            , applicationChildren = args
            }
      =
        let
            SymbolOrAlias { symbolOrAliasConstructor } = applicationSymbolOrAlias
            Id { getId = attrId } = symbolOrAliasConstructor
            insertOrUpdateOccurrences =
                Just . \case
                    Just alreadyOccurred ->
                        -- The attribute has already occurred, so the newest
                        -- occurrence is added to the list.
                        -- The latest occurrence is added at the head of the
                        -- list to avoid traversing the list many times; this
                        -- is allowed because the order of attributes is not
                        -- significant (see _The Semantics of K_).
                        occurrence NonEmpty.:| NonEmpty.toList alreadyOccurred
                    Nothing ->
                        -- The attribute has not occurred before.
                        occurrence NonEmpty.:| []
              where
                occurrence = Occurrence args
        in
            pure (HashMap.alter insertOrUpdateOccurrences attrId attrMap)

{- | Wrap the parser in a context for the named attribute.

 -}
withContext
    :: String  -- ^ attribute name
    -> Parser a  -- ^ attribute parser
    -> Parser a
withContext attr = Kore.Error.withContext ("attribute '" ++ attr ++ "'")

{- | Collect the argument lists of each occurrence of the attribute.

  @parseAttribute@ signals failure if the attribute is not present or returns a
  'NonEmpty' list containing the argument lists at each occurrence of the
  attribute.

 -}
parseAttribute
    :: String  -- ^ attribute name
    -> Parser (NonEmpty Occurrence)
parseAttribute key =
    do
        attrMap <- Reader.ask
        case HashMap.lookup key attrMap of
            Nothing -> koreFail ("no attribute found matching: " ++ key)
            Just occurs -> pure occurs

{- | Parse a key-only attribute.

  A key-only attribute has no arguments. @parseKeyAttribute@ signals failure if
  the attribute is not present or if it is present with the wrong number of
  arguments.

  See also: 'hasKeyAttribute'

 -}
parseKeyAttribute
    :: String  -- ^ attribute name
    -> Parser ()
parseKeyAttribute key =
    parseAttribute key >>= withContext key . (oneOccurrence >=> noArguments)

{- | Is the key-only attribute present?

  A key-only attribute has no arguments. @hasKeyAttribute@ signals failure if
  the attribute is present with the wrong number of arguments.

  See also: 'parseKeyAttribute'

 -}
hasKeyAttribute :: String -> Parser Bool
hasKeyAttribute key =
    (present $> True) <|> (missing $> False)
  where
    present = parseKeyAttribute key
    missing = assertNoAttribute key

{- | Parse an attribute that takes one string argument.

  @parseStringAttribute@ signals failure if:

    * the attribute is not present,

    * the attribute is specified more than once, or

    * the attribute is not given exactly one argument, which must be a string.

  @parseStringAttribute@ returns the lone string argument of the named
  attribute.

 -}
parseStringAttribute :: String -> Parser String
parseStringAttribute key =
    parseAttribute key >>= withContext key . expectStringArgument
  where
    expectStringArgument :: NonEmpty Occurrence -> Parser String
    expectStringArgument =
        oneOccurrence
        >=> oneArgument
        >=> expectMetaPattern
        >=> expectLiteralString

    expectMetaPattern =
        \case
            KoreMetaPattern pat -> pure pat
            _ -> koreFail "expected meta pattern"

    expectLiteralString
        :: Pattern Meta Variable CommonKorePattern -> Parser String
    expectLiteralString =
        \case
            StringLiteralPattern (StringLiteral arg) -> pure arg
            _ -> koreFail "expected literal string argument"

{- | Signal parse failure if the attribute is present.

  Use 'assertNoAttribute' to differentiate the case of a missing attribute from
  an attribute without its correct arguments. For example, many attributes are
  optional, but must have a single string argument if present.

  See also: 'hasKeyAttribute'

 -}
assertNoAttribute :: String -> Parser ()
assertNoAttribute key =
    do
        exists <- (parseAttribute key $> True) <|> pure False
        when exists (koreFail ("expected no attribute '" ++ key ++ "'"))

{- | Fail if the attribute does not occur exactly once.

  @oneOccurrence@ returns the argument list of the attribute's one occurrence.

 -}
oneOccurrence :: NonEmpty a -> Parser a
oneOccurrence =
    \case
        args :| [] -> pure args
        _ -> koreFail "unexpected multiple occurrences"

{- | Fail if the attribute is given any arguments.
 -}
noArguments :: Occurrence -> Parser ()
noArguments (Occurrence args) =
    case args of
        [] -> pure ()
        _ -> koreFail "unexpected arguments"

{- | Fail if the attribute is not given exactly one argument.

  @oneArgument@ returns the attribute's one argument.

 -}
oneArgument :: Occurrence -> Parser CommonKorePattern
oneArgument (Occurrence args) =
    case args of
        [a] -> pure a
        _ -> koreFail "expected 1 argument"
