{- |
Module      : Kore.Attribute.Parser
Description : Attribute parsers
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
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
module Kore.Attribute.Parser (
    -- * Parsing attributes
    ParseAttributes (..),
    toAttributes,
    Attributes (..),
    Parser,
    ParseError,
    parseAttributes,
    parseAttributesWith,
    liftParser,

    -- * Parsers
    failDuplicate,
    failConflicting,
    parseBoolAttribute,
    parseBoolAttributeAux,
    toBoolAttributes,
    toBoolAttributesAux,
    withApplication,
    getZeroParams,
    getTwoParams,
    getZeroArguments,
    getOneArgument,
    getZeroOrOneArguments,
    getTwoArguments,
    getSymbolOrAlias,
    Kore.Attribute.Parser.getStringLiteral,
    getVariable,
    parseSExpr,
    parseReadS,
    parseStringLiteral,
    parseInteger,

    -- * Re-exports
    AttributePattern,
    asAttributePattern,
    attributePattern,
    attributePattern_,
    attributeString,
    attributeInteger,
    attributeVariable,
    Default (..),
    StringLiteral (StringLiteral),
    Generic,
    NFData,
    module Kore.AST.Common,
    module Kore.Sort,
    module Kore.Syntax.Application,
) where

import Control.Lens (
    Getter,
    Iso',
 )
import Control.Lens qualified as Lens
import Control.Monad.Except (
    MonadError,
 )
import Control.Monad.Except qualified as Monad.Except
import Data.Coerce
import Data.Default (
    Default (..),
 )
import Data.Default qualified as Default
import Data.Functor.Foldable qualified as Recursive
import Data.List qualified as List
import Data.Text (
    Text,
 )
import Data.Text qualified as Text
import GHC.Generics (
    Generic,
 )
import Kore.AST.Common
import Kore.AST.Error qualified as Kore.Error
import Kore.Attribute.Attributes
import Kore.Attribute.Null qualified as Attribute (
    Null,
 )
import Kore.Error (
    Error,
    castError,
 )
import Kore.Error qualified
import Kore.Sort
import Kore.Syntax.Application
import Kore.Syntax.Pattern
import Kore.Syntax.StringLiteral (
    StringLiteral (StringLiteral),
 )
import Kore.Syntax.Variable (
    SomeVariable,
    VariableName,
 )
import Prelude.Kore
import SMT.SimpleSMT (
    SExpr,
    readSExprs,
 )

data ParseError

type Parser = Either (Error ParseError)

class (Default attrs, From attrs Attributes) => ParseAttributes attrs where
    -- | Parse a 'AttributePattern' from 'Attributes' to produce @attrs@.
    --
    --    Attributes are parsed individually and the list of attributes is parsed by
    --    folding over the list; @parseAttributes@ takes a second argument which is
    --    the partial result obtained by folding over the preceeding attributes of the
    --    list.
    --
    --    Ignore unrecognized attributes by 'return'-ing the partial result. Signal
    --    errors with 'Control.Monad.Except.throwError' to abort parsing.
    --
    --    See also: 'parseAttributes', 'withApplication', 'runParser'
    parseAttribute ::
        -- | attribute
        AttributePattern ->
        -- | partial parsing result
        attrs ->
        Parser attrs

toAttributes :: forall attrs. From attrs Attributes => attrs -> Attributes
toAttributes = from

instance ParseAttributes Attributes where
    parseAttribute attr (Attributes attrs) =
        return (Attributes $ attr : attrs)

instance ParseAttributes Attribute.Null where
    parseAttribute _ _ = return mempty

parseAttributesWith ::
    ParseAttributes attrs =>
    Attributes ->
    attrs ->
    Parser attrs
parseAttributesWith (Attributes attrs) def' =
    foldlM (flip parseAttribute) def' attrs

parseAttributes :: ParseAttributes attrs => Attributes -> Parser attrs
parseAttributes attrs = parseAttributesWith attrs Default.def

-- | Run an attribute parser in any 'MonadError' with the given initial state.
liftParser ::
    MonadError (Error e) m =>
    -- | parser
    Parser a ->
    m a
liftParser = Monad.Except.liftEither . Kore.Error.castError

-- | Fail due to a duplicate attribute.
failDuplicate :: Id -> Parser a
failDuplicate ident =
    Kore.Error.koreFail ("duplicate attribute: " ++ getIdForError ident)

-- | Fail due to conflicting attributes.
failConflicting :: [Id] -> Parser a
failConflicting idents =
    Kore.Error.koreFail
        ( "conflicting attributes: "
            ++ List.intercalate ", " (getIdForError <$> idents)
        )

toBoolAttributes ::
    Coercible attr Bool => AttributePattern -> attr -> Attributes
toBoolAttributes = toBoolAttributesAux Lens.coerced

toBoolAttributesAux ::
    Getter attr Bool -> AttributePattern -> attr -> Attributes
toBoolAttributesAux asBool pattern1 attr =
    Attributes [pattern1 | Lens.view asBool attr]

parseBoolAttribute ::
    Coercible attr Bool =>
    Id ->
    AttributePattern ->
    attr ->
    Parser attr
parseBoolAttribute = parseBoolAttributeAux Lens.coerced

parseBoolAttributeAux ::
    Iso' attr Bool -> Id -> AttributePattern -> attr -> Parser attr
parseBoolAttributeAux asBool ident =
    withApplication' $ \params args attr -> do
        getZeroParams params
        getZeroArguments args
        when (Lens.view asBool attr) failDuplicate'
        return (Lens.review asBool True)
  where
    withApplication' = withApplication ident
    failDuplicate' = failDuplicate ident

withApplication ::
    Id ->
    ([Sort] -> [AttributePattern] -> attrs -> Parser attrs) ->
    AttributePattern ->
    attrs ->
    Parser attrs
withApplication ident go kore =
    case Recursive.project kore of
        _ :< ApplicationF app
            | symbolOrAliasConstructor == ident ->
                Kore.Error.withLocationAndContext symbol context
                    . go symbolOrAliasParams applicationChildren
          where
            ~context = "attribute '" <> Text.pack (show symbol) <> "'"
            Application{applicationSymbolOrAlias = symbol} = app
            Application{applicationChildren} = app
            SymbolOrAlias{symbolOrAliasConstructor} = symbol
            SymbolOrAlias{symbolOrAliasParams} = symbol
        _ -> return

getZeroParams :: [Sort] -> Parser ()
getZeroParams =
    \case
        [] -> return ()
        params ->
            Kore.Error.koreFailWithLocations
                params
                ("expected zero parameters, found " <> Text.pack (show arity))
          where
            arity = length params

getTwoParams :: [Sort] -> Parser (Sort, Sort)
getTwoParams =
    \case
        [param1, param2] -> return (param1, param2)
        params ->
            Kore.Error.koreFailWithLocations
                params
                ("expected two parameters, found " <> Text.pack (show arity))
          where
            arity = length params

-- | Accept exactly zero arguments.
getZeroArguments ::
    [AttributePattern] ->
    Parser ()
getZeroArguments =
    \case
        [] -> return ()
        args ->
            Kore.Error.koreFail
                ("expected zero arguments, found " ++ show arity)
          where
            arity = length args

-- | Accept exactly one argument.
getOneArgument ::
    [AttributePattern] ->
    Parser AttributePattern
getOneArgument =
    \case
        [arg] -> return arg
        args ->
            Kore.Error.koreFail
                ("expected one argument, found " ++ show arity)
          where
            arity = length args

getZeroOrOneArguments ::
    [AttributePattern] ->
    Parser (Maybe AttributePattern)
getZeroOrOneArguments =
    \case
        [] -> return Nothing
        [arg] -> return (Just arg)
        args ->
            Kore.Error.koreFail
                ("expected at most one argument, found " <> show arity)
          where
            arity = length args

-- | Accept exactly two arguments.
getTwoArguments ::
    [AttributePattern] ->
    Parser (AttributePattern, AttributePattern)
getTwoArguments =
    \case
        [arg1, arg2] -> return (arg1, arg2)
        args ->
            Kore.Error.koreFail
                ("expected two arguments, found " ++ show arity)
          where
            arity = length args

-- | Accept a symbol or alias applied to no arguments.
getSymbolOrAlias :: AttributePattern -> Parser SymbolOrAlias
getSymbolOrAlias kore =
    case Recursive.project kore of
        _ :< ApplicationF app
            | [] <- applicationChildren -> return symbol
            | otherwise ->
                Kore.Error.withLocationAndContext
                    symbol
                    ("symbol '" <> Text.pack (show symbol) <> "'")
                    (Kore.Error.koreFail "expected zero arguments")
          where
            Application{applicationSymbolOrAlias = symbol} = app
            Application{applicationChildren} = app
        _ -> Kore.Error.koreFail "expected symbol or alias application"

-- | Accept a string literal.
getStringLiteral :: AttributePattern -> Parser StringLiteral
getStringLiteral kore =
    case Recursive.project kore of
        _ :< StringLiteralF (Const lit) -> return lit
        _ -> Kore.Error.koreFail "expected string literal pattern"

-- | Accept a variable.
getVariable :: AttributePattern -> Parser (SomeVariable VariableName)
getVariable kore =
    case Recursive.project kore of
        _ :< VariableF (Const var) -> return var
        _ -> Kore.Error.koreFail "expected variable pattern"

{- | Parse a 'Text' through 'ReadS'.

See also: 'parseInteger'
-}
parseReadS :: ReadS a -> Text -> Parser a
parseReadS aReadS (Text.unpack -> syntax) =
    case aReadS syntax of
        [] -> noParse
        r : rs ->
            case rs of
                _ : _ -> ambiguousParse
                _
                    | null unparsed -> return a
                    | otherwise -> incompleteParse unparsed
          where
            (a, unparsed) = r
  where
    noParse = Kore.Error.koreFail ("failed to parse \"" ++ syntax ++ "\"")
    ambiguousParse =
        Kore.Error.koreFail $
            "parsing \"" ++ syntax ++ "\" was ambiguous"
    incompleteParse unparsed =
        Kore.Error.koreFail $
            "incomplete parse: failed to parse \"" ++ unparsed ++ "\""

-- | Parse an 'Integer' from a 'StringLiteral'.
parseInteger :: StringLiteral -> Parser Integer
parseInteger = parseStringLiteral reads

-- | Parse from a 'StringLiteral'.
parseStringLiteral :: ReadS a -> StringLiteral -> Parser a
parseStringLiteral reads' (StringLiteral literal) = parseReadS reads' literal

{- | Parse an 'SExpr' for the @smtlib@ attribute.

An error is signalled in 'Parser' if we cannot parse the 'SExpr', or if the
entire argument is not consumed by the parser.
-}
parseSExpr ::
    -- | text representing an 'SExpr'
    Text ->
    Parser SExpr
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
