{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}

{-# Options -Wno-partial-fields #-}

module KoreJson (
    ) where

--    KorePattern(..)

import Data.Aeson as Json
import Data.Aeson.Encode.Pretty as Json
import Data.ByteString.Lazy (ByteString)
import Data.Char (toLower)
import Data.Either.Extra
import Data.Text (Text)
import GHC.Generics
import Kore.Attribute.Attributes (ParsedPattern)
import Kore.Internal.Pattern (Pattern)
import Prelude

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
        , sort :: Sort
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
    | -- | domain value, a string literal. ???
      KJDomainValue {value :: Text}
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

data Sort = Sort
    { name :: Id -- may start by a backslash
    , args :: [Sort]
    }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

-- TODO could omit the args field if empty (custom instance)

-- names and arity of known ML connectives
data Connective
    = Top
    | Bottom
    | Not
    | And
    | Or
    | Implies
    | Iff
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

-- TODO are these string-tag encoded in the generated instance?

connArity :: Connective -> Int
connArity Top = 0
connArity Bottom = 0
connArity Not = 1
connArity And = 2
connArity Or = 2
connArity Implies = 2
connArity Iff = 2

--
data Quant
    = Forall
    | Exists
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

data Fix
    = Mu
    | Nu
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

data Pred
    = Ceil
    | Floor
    | Equals
    | In
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

data LeftRight
    = Left
    | Right
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

--------------------------------------------------
-- parsing utilities

-- | low-level: read text into KorePattern
decodeKoreJson :: ByteString -> Either String KorePattern
decodeKoreJson = Json.eitherDecode'

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
    | -- | Inconsistent data parsed. TODO: refine!
      KoreError String

toParsedPattern :: KorePattern -> Either JsonError ParsedPattern
toParsedPattern x = Prelude.Left (KoreError $ "not implemented: " ++ show x)

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
