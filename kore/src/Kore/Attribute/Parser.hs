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

import qualified Control.Monad as Monad
import           Control.Monad.Except
                 ( MonadError )
import qualified Control.Monad.Except as Monad.Except
import           Data.Default
                 ( Default )
import qualified Data.Default as Default
import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive
import qualified Data.List as List
import qualified Data.Maybe as Maybe
import           Data.Text
                 ( Text )

import qualified Kore.AST.Error as Kore.Error
import           Kore.AST.Kore hiding
                 ( getStringLiteral )
import           Kore.AST.Sentence
                 ( Attributes (Attributes) )
import qualified Kore.Attribute.Hook.Hook as Attribute
import qualified Kore.Attribute.Smtlib.Smtlib as Attribute
import qualified Kore.Attribute.Sort as Attribute
import qualified Kore.Attribute.Sort.Concat as Attribute.Sort
import qualified Kore.Attribute.Sort.Element as Attribute.Sort
import qualified Kore.Attribute.Sort.Unit as Attribute.Sort
import           Kore.Error
                 ( Error, castError )
import qualified Kore.Error
import           SimpleSMT
                 ( SExpr, readSExprs )

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
getStringLiteral :: CommonKorePattern -> Parser StringLiteral
getStringLiteral kore =
    case Recursive.project kore of
        _ :< UnifiedObjectPattern (StringLiteralPattern lit) -> return lit
        _ -> Kore.Error.koreFail "expected string literal pattern"

instance ParseAttributes Attribute.Sort where
    parseAttribute attr =
        Attribute.lensHook (parseAttribute attr)
        Monad.>=> Attribute.lensSmtlib (parseAttribute attr)
        Monad.>=> Attribute.lensUnit (parseAttribute attr)
        Monad.>=> Attribute.lensElement (parseAttribute attr)
        Monad.>=> Attribute.lensConcat (parseAttribute attr)

{- | Parse the @hook@ Kore attribute, if present.

  It is a parse error if the @hook@ attribute is not given exactly one literal
  string argument.

  See also: 'hookAttribute'

 -}
instance ParseAttributes Attribute.Hook where
    parseAttribute =
        withApplication' $ \params args (Attribute.Hook hook) -> do
            getZeroParams params
            arg <- getOneArgument args
            StringLiteral name <- getStringLiteral arg
            Monad.unless (Maybe.isNothing hook) failDuplicate'
            return Attribute.Hook { getHook = Just name }
      where
        withApplication' = withApplication Attribute.hookId
        failDuplicate' = failDuplicate Attribute.hookId

{- | Parse an 'SExpr' for the @smtlib@ attribute.

An error is signalled in 'Parser' if we cannot parse the 'SExpr', or if the
entire argument is not consumed by the parser.

 -}
parseSExpr
    :: Text  -- ^ text representing an 'SExpr'
    -> Parser SExpr
parseSExpr syntax =
    case readSExprs syntax of
        [] -> noParse
        sExpr : rest ->
            case rest of
                [] -> return sExpr
                _ -> incompleteParse
  where
    noParse = Kore.Error.koreFail "failed to parse S-expression"
    incompleteParse = Kore.Error.koreFail "failed to parse entire argument"

instance ParseAttributes Attribute.Smtlib where
    parseAttribute =
        withApplication' $ \params args Attribute.Smtlib { getSmtlib } -> do
            getZeroParams params
            arg <- getOneArgument args
            StringLiteral syntax <- getStringLiteral arg
            sExpr <- parseSExpr syntax
            Monad.unless (Maybe.isNothing getSmtlib) failDuplicate'
            return Attribute.Smtlib { getSmtlib = Just sExpr }
      where
        withApplication' = withApplication Attribute.smtlibId
        failDuplicate' = failDuplicate Attribute.smtlibId

instance ParseAttributes Attribute.Sort.Unit where
    parseAttribute = withApplication' parseApplication
      where
        parseApplication params args Attribute.Sort.Unit { getUnit }
          | Just _ <- getUnit = failDuplicate'
          | otherwise = do
            getZeroParams params
            arg <- getOneArgument args
            symbol <- getSymbolOrAlias arg
            return Attribute.Sort.Unit { getUnit = Just symbol }
        withApplication' = withApplication Attribute.Sort.unitId
        failDuplicate' = failDuplicate Attribute.Sort.unitId

instance ParseAttributes Attribute.Sort.Element where
    parseAttribute = withApplication' parseApplication
      where
        parseApplication params args Attribute.Sort.Element { getElement }
          | Just _ <- getElement = failDuplicate'
          | otherwise = do
            getZeroParams params
            arg <- getOneArgument args
            symbol <- getSymbolOrAlias arg
            return Attribute.Sort.Element { getElement = Just symbol }
        withApplication' = withApplication Attribute.Sort.elementId
        failDuplicate' = failDuplicate Attribute.Sort.elementId

instance ParseAttributes Attribute.Sort.Concat where
    parseAttribute = withApplication' parseApplication
      where
        parseApplication params args Attribute.Sort.Concat { getConcat }
          | Just _ <- getConcat = failDuplicate'
          | otherwise = do
            getZeroParams params
            arg <- getOneArgument args
            symbol <- getSymbolOrAlias arg
            return Attribute.Sort.Concat { getConcat = Just symbol }
        withApplication' = withApplication Attribute.Sort.concatId
        failDuplicate' = failDuplicate Attribute.Sort.concatId
