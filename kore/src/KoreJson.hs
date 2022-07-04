{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}

{-# Options -Wno-partial-fields #-}

module KoreJson (
    ) where

import Data.Aeson as Json
import Data.Aeson.Encode.Pretty as Json
import Data.ByteString.Lazy (ByteString)
import Data.Char (toLower)
import Data.Either.Extra
import Data.Functor.Const (Const (..))
import Data.Text (Text)
import GHC.Generics -- FIXME switch to TH-generated Json instances
import Kore.Attribute.Attributes (ParsedPattern)
import Kore.Internal.Pattern (Pattern)
import Kore.Syntax.PatternF (PatternF (..))
-- import Kore.Internal.TermLike.TermLike (TermLikeF(..))
import Kore.Parser (embedParsedPattern)
import Kore.Sort qualified as Kore
import Kore.Syntax qualified as Kore
import Kore.Syntax.Variable (ElementVariableName (..), SetVariableName (..), SomeVariableName (..), Variable (..), VariableName (..))
import Prelude.Kore as Prelude

{- | Json representation of Kore patterns as a Haskell type.
 Modeled after kore-syntax.md, merging some of the ML pattern
 productions. Cursorily checked to be consistent with Parser.y
-}
data KorePattern
    = -- variable pattern

      -- | element variable with sort
      KJEVar
        { name :: Id
        , sort :: Sort
        }
    | -- | set variable with sort
      KJSVar
        { name :: Id -- must start by '@'
        , sort :: Sort
        }
    | -- application pattern

      -- | application pattern (symbol, [arg] )
      KJApp
        { name :: Id -- may start by a '\\'
        , sorts :: [Sort]
        , args :: [KorePattern]
        }
    | -- | string literal
      KJString Text
    | -- matching logic pattern

      -- | Connective (top, bottom, not, and, or, implies, iff)
      KJConnective
        { conn :: Connective
        , sort :: Sort
        , args :: [KorePattern] -- arg count checked in conversion to TermLike, not here
        }
    | -- | Quantifiers: forall, exists
      KJQuantifier
        { quant :: Quant
        , sort :: Sort
        , var :: Id
        , varSort :: Sort
        , arg :: KorePattern
        }
    | -- | mu, nu
      KJFixpoint
        { combinator :: Fix
        , -- no sort
          var :: Id
        , varSort :: Sort
        , arg :: KorePattern
        }
    | -- | ceil, floor, equals, in. NOTE these do not really fit together
      -- nicely... the two sorts have vastly different meaning
      KJPredicate
        { pred :: Pred
        , sort :: Sort
        , sort2 :: Sort
        , args :: [KorePattern]
        }
    | -- next, rewrites

      -- | goes to 'dest' next
      KJNext
        { sort :: Sort
        , dest :: KorePattern
        }
    | -- | source rewrites to dest (same sort)
      KJRewrites
        { sort :: Sort
        , source :: KorePattern
        , dest :: KorePattern
        }
    | -- | domain value, a string literal with a sort
      KJDomainValue
        { sort :: Sort
        , value :: Text
        }
    | -- syntactic sugar

      -- | left/right associative or-cascade
      KJMultiOr
        { assoc :: LeftRight
        , args :: [KorePattern]
        }
    | -- | left/right associative app pattern
      KJMultiApp
        { assoc :: LeftRight
        , symbol :: Id -- may start by a '\\'
        , sort :: Sort
        , args :: [KorePattern]
        }
    deriving stock (Eq, Show, Generic)

instance ToJSON KorePattern where
    toJSON = genericToJSON codecOptions

instance FromJSON KorePattern where
    parseJSON = genericParseJSON codecOptions

codecOptions :: Json.Options
codecOptions =
    Json.defaultOptions
        { constructorTagModifier
        , omitNothingFields = True
        , sumEncoding = ObjectWithSingleField
        , unwrapUnaryRecords = True
        , tagSingleConstructors = True
        , rejectUnknownFields = True
        }
  where
    constructorTagModifier = \case
        'K' : 'J' : x : rest -> toLower x : rest
        x : rest -> toLower x : rest
        [] -> [] -- can happen on rogue json input

newtype Id = Id Text
    deriving stock (Eq, Show, Generic)
    deriving newtype (ToJSON, FromJSON)

data Sort
    = Sort
        { name :: Id -- may start by a backslash
        , args :: [Sort]
        }
    | SortVariable Text -- may start by a backslash
    deriving stock (Eq, Show, Generic)

instance ToJSON Sort where
    toJSON = genericToJSON codecOptions{sumEncoding = UntaggedValue}

instance FromJSON Sort where
    parseJSON = genericParseJSON codecOptions{sumEncoding = UntaggedValue}

-- TODO could omit the args field if empty (custom instance)

-- names of known ML connectives. Arity checked during conversion
data Connective
    = Top
    | Bottom
    | Not
    | And
    | Or
    | Implies
    | Iff
    deriving stock (Eq, Show, Generic, Enum, Bounded)
    deriving anyclass (ToJSON, FromJSON)

-- string-tag encoded in the generated instance. Should they be lower-case?

data Quant
    = Forall
    | Exists
    deriving stock (Eq, Show, Generic, Enum, Bounded)
    deriving anyclass (ToJSON, FromJSON)

data Fix
    = Mu
    | Nu
    deriving stock (Eq, Show, Generic, Enum, Bounded)
    deriving anyclass (ToJSON, FromJSON)

data Pred
    = Ceil
    | Floor
    | Equals
    | In
    deriving stock (Eq, Show, Generic, Enum, Bounded)
    deriving anyclass (ToJSON, FromJSON)

data LeftRight
    = Left
    | Right
    deriving stock (Eq, Show, Generic, Enum, Bounded)
    deriving anyclass (ToJSON, FromJSON)

------------------------------------------------------------
-- reading

{- | read text into KorePattern, then check for consistency and
 construct a ParsedPattern
-}
decodePattern :: ByteString -> Either JsonError ParsedPattern
decodePattern bs =
    mapLeft ParseError (decodeKoreJson bs) >>= toParsedPattern

-- | Errors relating to the json codec
data JsonError
    = -- | Problem reported by json parser
      ParseError String
    | -- | Wrong arg count for a connective or other construct
      WrongArgCount String Int
    | -- | Inconsistent data parsed. TODO: refine!
      KoreError String
    | NotImplemented String

-- | low-level: read text into KorePattern
decodeKoreJson :: ByteString -> Either String KorePattern
decodeKoreJson = Json.eitherDecode'

-- see Parser.y
toParsedPattern :: KorePattern -> Either JsonError ParsedPattern
toParsedPattern = \case
    KJEVar n s ->
      embedVar (SomeVariableNameElement . ElementVariableName) n s

    KJSVar n s ->
      embedVar (SomeVariableNameSet . SetVariableName) n s

    KJApp n ss as ->
      fmap (embedParsedPattern . ApplicationF) $
      Kore.Application <$> toSymbol n ss <*> traverse toParsedPattern as

    KJString t ->
      embedParsedPattern . StringLiteralF . Const <$> pure (Kore.StringLiteral t)

    KJConnective c s as ->
      embedParsedPattern <$> mkConnective c s as

    x -> todo $ show x

  where
    todo = Prelude.Left . NotImplemented

    embedVar :: (VariableName -> SomeVariableName VariableName)
             -> Id -> Sort -> Either JsonError ParsedPattern
    embedVar cons n s =
      fmap (embedParsedPattern . VariableF . Const) $
      Variable <$> mkVarName cons n <*> mkSort s

    mkVarName :: (VariableName -> SomeVariableName VariableName)
            -> Id
            -> Either JsonError (SomeVariableName VariableName)
    mkVarName embed = pure . embed . flip VariableName Nothing . koreId

    toSymbol :: Id -> [Sort] -> Either JsonError Kore.SymbolOrAlias
    toSymbol n sorts = Kore.SymbolOrAlias <$> pure (koreId n) <*> traverse mkSort sorts

-- TODO check well-formed (initial letter, char. set)
-- FIXME do we need to read a numeric suffix? (-> Parser.y:getVariableName)

koreId :: Id -> Kore.Id
koreId (Id name) = Kore.Id name Kore.AstLocationNone

mkSort :: Sort -> Either JsonError Kore.Sort
mkSort Sort{name, args} =
  fmap (Kore.SortActualSort . Kore.SortActual (koreId name)) $
  mapM mkSort args
mkSort (SortVariable name) =
  pure . Kore.SortVariableSort $ Kore.SortVariable (koreId $ Id name)

mkConnective :: Connective
             -> Sort
             -> [KorePattern]
             -> Either JsonError (PatternF VariableName ParsedPattern)
mkConnective Top s [] =
  TopF . Kore.Top <$> (mkSort s)
mkConnective Bottom s [] =
  BottomF . Kore.Bottom <$> (mkSort s)
mkConnective Not s [a] =
  fmap NotF $
  Kore.Not <$> mkSort s <*> toParsedPattern a
mkConnective And s [a,b] =
  fmap AndF $
  Kore.And <$> mkSort s <*> toParsedPattern a <*> toParsedPattern b
mkConnective Or s [a,b] =
  fmap OrF $
  Kore.Or <$> mkSort s <*> toParsedPattern a <*> toParsedPattern b
mkConnective Implies s [a,b] =
  fmap ImpliesF $
  Kore.Implies <$> mkSort s <*> toParsedPattern a <*> toParsedPattern b
mkConnective Iff s [a,b] =
  fmap IffF $
  Kore.Iff <$> mkSort s <*> toParsedPattern a <*> toParsedPattern b
-- fall-through cases because of wrong argument count
mkConnective conn _ as = Prelude.Left $ WrongArgCount (show conn) (length as)


------------------------------------------------------------
-- writing

-- | Write a Pattern to a json byte string
encodePattern :: Pattern a -> ByteString
encodePattern = encodeKoreJson . fromParsedPattern

encodeKoreJson :: KorePattern -> ByteString
encodeKoreJson = Json.encodePretty' prettyJsonOpts
  where
    prettyJsonOpts =
        defConfig
            { confIndent = Spaces 2
            , confCompare = argsLast
            }
    argsLast :: Text -> Text -> Ordering
    argsLast "args" "args" = EQ
    argsLast "args" _ = GT
    argsLast _ "args" = LT
    argsLast x y = compare x y

fromParsedPattern :: Pattern a -> KorePattern
fromParsedPattern _ = error "not implemented"
