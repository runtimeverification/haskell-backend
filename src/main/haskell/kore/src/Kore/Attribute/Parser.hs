{-|
Module      : Kore.Attribute.Parser
Description : Attribute parsers
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
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
      ParseAttributes (..)
    , Attributes (..)
    , Parser
    , ParseError
    , parseAttributes
    , parseAttributesWith
    , liftParser
      -- * Parsers
    , failDuplicate
    , failConflicting
    , withApplication
    , getZeroParams
    , getTwoParams
    , getZeroArguments
    , getOneArgument
    , getTwoArguments
    , getSymbolOrAlias
    , Kore.Attribute.Parser.getStringLiteral
    ) where

import           Control.Monad.Except
                 ( MonadError )
import qualified Control.Monad.Except as Monad.Except
import           Data.Default
                 ( Default )
import qualified Data.Default as Default
import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive
import qualified Data.List as List

import qualified Kore.AST.Error as Kore.Error
import           Kore.AST.Kore
import           Kore.AST.Sentence
                 ( Attributes (Attributes) )
import           Kore.Error
                 ( Error, castError )
import qualified Kore.Error

data ParseError

type Parser = Either (Error ParseError)

class Default attrs => ParseAttributes attrs where
    {- | Parse a 'CommonKorePattern' from 'Attributes' to produce @attrs@.

    Attributes are parsed individually and the list of attributes is parsed by
    folding over the list; @parseAttributes@ takes a second argument which is
    the partial result obtained by folding over the preceeding attributes of the
    list.

    Ignore unrecognized attributes by 'return'-ing the partial result. Signal
    errors with 'Control.Monad.Except.throwError' to abort parsing.

    See also: 'parseAttributes', 'withApplication', 'runParser'

     -}
    parseAttribute
        :: CommonKorePattern  -- ^ attribute
        -> attrs  -- ^ partial parsing result
        -> Parser attrs

instance ParseAttributes Attributes where
    parseAttribute attr (Attributes attrs) =
        return (Attributes $ attr : attrs)

parseAttributesWith
    :: ParseAttributes attrs
    => Attributes
    -> attrs
    -> Parser attrs
parseAttributesWith (Attributes attrs) def =
    Foldable.foldlM (flip parseAttribute) def attrs

parseAttributes :: ParseAttributes attrs => Attributes -> Parser attrs
parseAttributes attrs = parseAttributesWith attrs Default.def

-- | Run an attribute parser in any 'MonadError' with the given initial state.
liftParser
    :: MonadError (Error e) m
    => Parser a  -- ^ parser
    -> m a
liftParser = Monad.Except.liftEither . Kore.Error.castError

-- | Fail due to a duplicate attribute.
failDuplicate :: Id level -> Parser a
failDuplicate ident =
    Kore.Error.koreFail ("duplicate attribute: " ++ getIdForError ident)

-- | Fail due to conflicting attributes.
failConflicting :: [Id level] -> Parser a
failConflicting idents =
    Kore.Error.koreFail
        ("conflicting attributes: "
            ++ List.intercalate ", " (getIdForError <$> idents))

withApplication
    :: Id Object
    -> ([Sort Object] -> [CommonKorePattern] -> attrs -> Parser attrs)
    -> CommonKorePattern
    -> attrs
    -> Parser attrs
withApplication ident go kore =
    case Recursive.project kore of
        _ :< UnifiedObjectPattern (ApplicationPattern app)
          | symbolOrAliasConstructor == ident -> \attrs ->
            Kore.Error.withLocationAndContext
                symbol
                ("attribute '" ++ show symbol ++ "'")
                (go symbolOrAliasParams applicationChildren attrs)
          where
            Application { applicationSymbolOrAlias = symbol } = app
            Application { applicationChildren } = app
            SymbolOrAlias { symbolOrAliasConstructor } = symbol
            SymbolOrAlias { symbolOrAliasParams } = symbol
        _ -> return

getZeroParams :: [Sort Object] -> Parser ()
getZeroParams =
    \case
        [] -> return ()
        params ->
            Kore.Error.koreFailWithLocations params
                ("expected zero parameters, found " ++ show arity)
          where
            arity = length params

getTwoParams :: [Sort Object] -> Parser (Sort Object, Sort Object)
getTwoParams =
    \case
        [param1, param2] -> return (param1, param2)
        params ->
            Kore.Error.koreFailWithLocations params
                ("expected two parameters, found " ++ show arity)
          where
            arity = length params

{- | Accept exactly zero arguments.
 -}
getZeroArguments
    :: [CommonKorePattern]
    -> Parser ()
getZeroArguments =
    \case
        [] -> return ()
        args ->
            Kore.Error.koreFail
                ("expected zero arguments, found " ++ show arity)
          where
            arity = length args

{- | Accept exactly one argument.
 -}
getOneArgument
    :: [CommonKorePattern]
    -> Parser CommonKorePattern
getOneArgument =
    \case
        [arg] -> return arg
        args ->
            Kore.Error.koreFail
                ("expected one argument, found " ++ show arity)
          where
            arity = length args

{- | Accept exactly two arguments.
 -}
getTwoArguments
    :: [CommonKorePattern]
    -> Parser (CommonKorePattern, CommonKorePattern)
getTwoArguments =
    \case
        [arg1, arg2] -> return (arg1, arg2)
        args ->
            Kore.Error.koreFail
                ("expected two arguments, found " ++ show arity)
          where
            arity = length args

{- | Accept a symbol or alias applied to no arguments.
 -}
getSymbolOrAlias :: CommonKorePattern -> Parser (SymbolOrAlias Object)
getSymbolOrAlias kore =
    case Recursive.project kore of
        _ :< UnifiedObjectPattern (ApplicationPattern app)
          | [] <- applicationChildren -> return symbol
          | otherwise ->
            Kore.Error.withLocationAndContext
                symbol
                ("symbol '" ++ show symbol ++ "'")
                (Kore.Error.koreFail "expected zero arguments")
          where
            Application { applicationSymbolOrAlias = symbol } = app
            Application { applicationChildren } = app
        _ -> Kore.Error.koreFail "expected symbol or alias application"

{- | Accept a string literal.
 -}
getStringLiteral :: CommonKorePattern -> Parser (StringLiteral)
getStringLiteral kore =
    case Recursive.project kore of
        _ :< UnifiedMetaPattern (StringLiteralPattern lit) -> return lit
        _ -> Kore.Error.koreFail "expected string literal pattern"
