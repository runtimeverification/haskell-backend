{-# LANGUAGE OverloadedStrings #-}

{-# Options -Wno-partial-fields #-}

{- |
Copyright   : (c) Runtime Verification, 2019-2022
License     : BSD-3-Clause
-}
module Kore.Syntax.Json.Base (
    -- export everything for debugging and testing only
    module Kore.Syntax.Json.Base,
) where

import Data.Aeson as Json
import Data.Aeson.Types qualified as Json
import Data.Char (isAlpha, isDigit)
import Data.Foldable ()
import Data.List (nub)
import Data.List.NonEmpty qualified as NE
import Data.Text (Text)
import Data.Text qualified as T
import GHC.Generics (Generic)
------------------------------------------------------------

-- | Top-level boilerplate to version the format
data KoreJson = KoreJson
    { format :: KORE
    , version :: Version
    , term :: KorePattern
    }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

data KORE
    = KORE
    deriving stock (Eq, Show)

instance ToJSON KORE where
    toJSON = const $ String "KORE"

instance FromJSON KORE where
    parseJSON = withText "format tag" $ expect "KORE" KORE

{- | All supported version numbers as an enum
 (json encoding turns this into an int)
-}
data Version
    = -- | Version 1
      KJ1
    deriving stock (Eq, Show)

kj :: Num a => Int -> a
kj = fromIntegral

instance ToJSON Version where
    toJSON KJ1 = Number $ kj 1

instance FromJSON Version where
    parseJSON =
        withScientific "version" (expect (kj 1) KJ1)

expect :: (Show a, Eq a) => a -> b -> a -> Json.Parser b
expect expected parsed actual
    | actual == expected = pure parsed
    | otherwise = fail $ "expected " <> show expected

------------------------------------------------------------

{- | Json representation of Kore patterns as a Haskell type.
 Modeled after kore-syntax.md, merging some of the ML pattern
 productions.
-}
data KorePattern
    = -- variable pattern

      -- element variable with sort
      KJEVar
        { name :: Id
        , sort :: Sort
        }
    | -- set variable with sort
      KJSVar
        { name :: Id -- must start by '@'
        , sort :: Sort
        }
    | -- application pattern
      KJApp
        { name :: Id -- may start by a '\\'
        , sorts :: [Sort]
        , args :: [KorePattern]
        }
    | -- string literal
      KJString
        { value :: Text
        }
    | -- matching logic pattern

      -- | Connective (top, bottom, not, and, or, implies, iff)
      KJTop
        { sort :: Sort
        }
    | KJBottom
        { sort :: Sort
        }
    | KJNot
        { sort :: Sort
        , arg :: KorePattern
        }
    | KJAnd
        { sort :: Sort
        , first :: KorePattern
        , second :: KorePattern
        }
    | KJOr
        { sort :: Sort
        , first :: KorePattern
        , second :: KorePattern
        }
    | KJImplies
        { sort :: Sort
        , first :: KorePattern
        , second :: KorePattern
        }
    | KJIff
        { sort :: Sort
        , first :: KorePattern
        , second :: KorePattern
        }
    | -- Quantifiers: forall, exists
      KJForall
        { sort :: Sort
        , var :: Id
        , varSort :: Sort
        , arg :: KorePattern
        }
    | KJExists
        { sort :: Sort
        , var :: Id
        , varSort :: Sort
        , arg :: KorePattern
        }
    | -- mu, nu
      KJMu
        { var :: Id
        , varSort :: Sort
        , arg :: KorePattern
        }
    | KJNu
        { var :: Id
        , varSort :: Sort
        , arg :: KorePattern
        }
    | -- ceil, floor, equals, in
      KJCeil
        { argSort :: Sort
        , sort :: Sort
        , arg :: KorePattern
        }
    | KJFloor
        { argSort :: Sort
        , sort :: Sort
        , arg :: KorePattern
        }
    | KJEquals
        { argSort :: Sort
        , sort :: Sort
        , first :: KorePattern
        , second :: KorePattern
        }
    | KJIn
        { argSort :: Sort
        , sort :: Sort
        , first :: KorePattern
        , second :: KorePattern
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
      KJDV
        { sort :: Sort
        , value :: Text
        }
    | -- syntactic sugar

      -- | left/right associative or-cascade
      KJMultiOr
        { assoc :: LeftRight
        , sort :: Sort
        , argss :: NE.NonEmpty KorePattern
        }
    | -- TODO textual parser also understands And/Implies/Iff

      -- | left/right associative app pattern
      KJMultiApp
        { assoc :: LeftRight
        , symbol :: Id -- may start by a '\\'
        , sorts :: [Sort]
        , argss :: NE.NonEmpty KorePattern
        }
    deriving stock (Eq, Show, Generic)

instance ToJSON KorePattern where
    toJSON = genericToJSON codecOptions

instance FromJSON KorePattern where
    parseJSON v = genericParseJSON codecOptions v >>= lexicalCheck

codecOptions :: Json.Options
codecOptions =
    Json.defaultOptions
        { constructorTagModifier
        , omitNothingFields = True
        , sumEncoding = TaggedObject "tag" "contents"
        , unwrapUnaryRecords = True
        , tagSingleConstructors = True
        , rejectUnknownFields = True
        }
  where
    constructorTagModifier = \case
        'K' : 'J' : rest -> rest
        other -> other

----------------------------------------
-- Identifiers and lexical checks

newtype Id = Id Text
    deriving stock (Eq, Show)
    deriving newtype (ToJSON, FromJSON)

{- | Performs a (shallow, top-level, no recursion) lexical check of
 identifiers contained in the given node. For details see the check
 functions below.
-}
lexicalCheck :: KorePattern -> Json.Parser KorePattern
lexicalCheck p =
    case p of
        KJEVar{name = Id n} ->
            reportErrors n "element variable" checkIdChars
        KJSVar{name = Id n} ->
            reportErrors n "set variable" checkSVarName
        KJApp{name = Id n} ->
            reportErrors n "app symbol" checkSymbolName
        KJForall{var = Id name} ->
            reportErrors name "quantifier variable" checkIdChars
        KJExists{var = Id name} ->
            reportErrors name "quantifier variable" checkIdChars
        KJMu{var = Id name} ->
            reportErrors name "fixpoint expression variable" checkSVarName
        KJNu{var = Id name} ->
            reportErrors name "fixpoint expression variable" checkSVarName
        -- KJDV{value = txt} ->
        --     reportErrors txt "domain value string" checkStringChars
        -- KJString txt ->
        --     reportErrors txt "string literal" checkStringChars
        -- Input supports std Unicode (as per json spec). toJSON could
        -- check that only allowed escape sequences will be generated.
        KJMultiApp{symbol = Id n} ->
            reportErrors n "multi-app symbol" checkSymbolName
        _ -> pure p
  where
    reportErrors :: Text -> String -> (Text -> [String]) -> Json.Parser KorePattern
    reportErrors text kind check
        | null errors = pure p
        | otherwise =
            fail . unwords $
                [ "Lexical"
                , if length errors == 1 then "error" else "errors"
                , "in"
                , kind
                , ":"
                , T.unpack text
                ]
                    <> map ("* " <>) errors
      where
        errors = check text

{- | Basic identifiers start with letters and may contain letters,
 digits, - or '. Set variables start with '@' followed by a basic
 identifier. Symbol variables _may_ start by \, followed by a basic
 identifier.
-}
checkIdChars :: Text -> [String] -- list of lexical errors
checkIdChars name
    | T.null name = ["Empty"]
    | otherwise =
        ["Illegal initial character " <> show first | not $ isAlpha first]
        ++ [ "Contains illegal characters: " <> show (nub $ T.unpack illegalChars)
           | not $ T.null illegalChars
           ]
  where
    ~first = T.head name
    ~illegalChars = T.filter (not . isIdChar) $ T.tail name

isIdChar :: Char -> Bool
isIdChar c = isAlpha c || isDigit c || c `elem` ['-', '\'']

-- | Set variable names _have to_ start with `@`, followed by a valid identifier
checkSVarName :: Text -> [String]
checkSVarName name
    | T.null name = ["Empty"]
    | otherwise =
        ["Must start with `@'" | T.head name /= '@']
        <> checkIdChars (T.tail name)

-- | Symbols _may_ start by a backslash.
checkSymbolName :: Text -> [String]
checkSymbolName name
    | Nothing <- mbParts = ["Empty"]
    | Just ('\\', rest) <- mbParts = checkIdChars rest
    | otherwise = checkIdChars name
  where
    mbParts = T.uncons name

------------------------------------------------------------
data Sort
    = SortApp
        { name :: Id
        , args :: [Sort]
        }
    | SortVar
        { name :: Id
        }
    deriving stock (Eq, Show, Generic)

instance ToJSON Sort where
    toJSON = genericToJSON codecOptions

instance FromJSON Sort where
    parseJSON = genericParseJSON codecOptions

data LeftRight
    = Left
    | Right
    deriving stock (Eq, Show, Generic, Enum, Bounded)
    deriving anyclass (ToJSON, FromJSON)
