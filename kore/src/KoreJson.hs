{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}

{-# Options -Wno-partial-fields #-}
{-# Options -Wno-duplicate-exports #-}
-- while exporting the entire module

module KoreJson (
    -- API
    JsonError (..),
    encodePattern,
    decodePattern,
    -- export everything for debugging and testing only
    module KoreJson,
) where

import Data.Aeson as Json
import Data.Aeson.Encode.Pretty as Json
import Data.ByteString.Lazy (ByteString)
import Data.Char (toLower)
import Data.Either.Extra hiding (Left, Right)
import Data.Functor.Const (Const (..))
import Data.List (foldl1')
import Data.Text (Text)
import GHC.Generics -- FIXME switch to TH-generated Json instances
import Kore.Attribute.Attributes (ParsedPattern)
import Kore.Parser (embedParsedPattern)
import Kore.Sort qualified as Kore
import Kore.Syntax qualified as Kore
import Kore.Syntax.PatternF (PatternF (..))
import Kore.Syntax.Variable (
    ElementVariableName (..),
    SetVariableName (..),
    SomeVariableName (..),
    Variable (..),
    VariableName (..),
 )
import Prelude.Kore hiding (Left, Right, pred)
import Prelude.Kore qualified as Prelude (Either (..))

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
        , sort :: Sort
        , args :: [KorePattern]
        }
    | -- TODO textual parser also understands And/Implies/Iff

      -- | left/right associative app pattern
      KJMultiApp
        { assoc :: LeftRight
        , symbol :: Id -- may start by a '\\'
        , sorts :: [Sort]
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
        fmap (embedParsedPattern . VariableF . Const) $
            embedVar (SomeVariableNameElement . ElementVariableName) n s
    KJSVar n s ->
        fmap (embedParsedPattern . VariableF . Const) $
            embedVar (SomeVariableNameSet . SetVariableName) n s
    KJApp n ss as ->
        fmap (embedParsedPattern . ApplicationF) $
            Kore.Application <$> toSymbol n ss <*> traverse toParsedPattern as
    KJString t ->
        embedParsedPattern . StringLiteralF . Const <$> pure (Kore.StringLiteral t)
    KJConnective c s as ->
        embedParsedPattern <$> mkConnective c s as
    KJQuantifier{quant = Forall, sort, var, varSort, arg} ->
        fmap (embedParsedPattern . ForallF) $
            Kore.Forall
                <$> mkSort sort
                <*> (Variable (ElementVariableName (koreVar var)) <$> mkSort varSort)
                <*> toParsedPattern arg
    KJQuantifier{quant = Exists, sort, var, varSort, arg} ->
        fmap (embedParsedPattern . ExistsF) $
            Kore.Exists
                <$> mkSort sort
                <*> (Variable (ElementVariableName (koreVar var)) <$> mkSort varSort)
                <*> toParsedPattern arg
    KJFixpoint{combinator = Mu, var, varSort, arg} ->
        fmap (embedParsedPattern . MuF) $
            Kore.Mu
                <$> (Variable (SetVariableName (koreVar var)) <$> mkSort varSort)
                <*> toParsedPattern arg
    KJFixpoint{combinator = Nu, var, varSort, arg} ->
        fmap (embedParsedPattern . NuF) $
            Kore.Nu
                <$> (Variable (SetVariableName (koreVar var)) <$> mkSort varSort)
                <*> toParsedPattern arg
    KJPredicate{pred, sort, sort2, args} ->
        embedParsedPattern <$> mkPredicate pred sort sort2 args
    KJNext{sort, dest} ->
        fmap (embedParsedPattern . NextF) $
            Kore.Next
                <$> mkSort sort
                <*> toParsedPattern dest
    KJRewrites{sort, source, dest} ->
        fmap (embedParsedPattern . RewritesF) $
            Kore.Rewrites
                <$> mkSort sort
                <*> toParsedPattern source
                <*> toParsedPattern dest
    KJDomainValue{sort, value} ->
        fmap (embedParsedPattern . DomainValueF) $
            Kore.DomainValue
                <$> mkSort sort
                <*> toParsedPattern (KJString value)
    KJMultiOr{assoc, sort, args} ->
        withAssoc assoc <$> mkOr sort <*> traverse toParsedPattern args
    KJMultiApp{assoc, symbol, sorts, args} ->
        withAssoc assoc <$> mkF symbol sorts <*> traverse toParsedPattern args
  where
    embedVar ::
        (VariableName -> SomeVariableName VariableName) ->
        Id ->
        Sort ->
        Either JsonError (Variable (SomeVariableName VariableName))
    embedVar cons n s =
        Variable <$> mkVarName cons n <*> mkSort s

    mkVarName ::
        (VariableName -> SomeVariableName VariableName) ->
        Id ->
        Either JsonError (SomeVariableName VariableName)
    mkVarName embed = pure . embed . koreVar

    toSymbol :: Id -> [Sort] -> Either JsonError Kore.SymbolOrAlias
    toSymbol n sorts = Kore.SymbolOrAlias <$> pure (koreId n) <*> traverse mkSort sorts

    withAssoc :: LeftRight -> (a -> a -> a) -> [a] -> a
    withAssoc Left = foldl1'
    withAssoc Right = foldr1

    mkOr :: Sort -> Either JsonError (ParsedPattern -> ParsedPattern -> ParsedPattern)
    mkOr s = do
        sort <- mkSort s
        pure (\a b -> embedParsedPattern $ OrF $ Kore.Or sort a b)

    mkF :: Id -> [Sort] -> Either JsonError (ParsedPattern -> ParsedPattern -> ParsedPattern)
    mkF n sorts = do
        sym <- toSymbol n sorts -- TODO should maybe check that length ss == 2?
        pure (\a b -> embedParsedPattern $ ApplicationF $ Kore.Application sym [a, b])

koreId :: Id -> Kore.Id
koreId (Id name) = Kore.Id name Kore.AstLocationNone

koreVar :: Id -> Kore.VariableName
koreVar = flip VariableName Nothing . koreId

-- TODO check well-formed (initial letter, char. set)
-- FIXME do we need to read a numeric suffix? (-> Parser.y:getVariableName)

mkSort :: Sort -> Either JsonError Kore.Sort
mkSort Sort{name, args} =
    fmap (Kore.SortActualSort . Kore.SortActual (koreId name)) $
        mapM mkSort args
mkSort (SortVariable name) =
    pure . Kore.SortVariableSort $ Kore.SortVariable (koreId $ Id name)

mkConnective ::
    Connective ->
    Sort ->
    [KorePattern] ->
    Either JsonError (PatternF VariableName ParsedPattern)
mkConnective Top s [] =
    TopF . Kore.Top <$> (mkSort s)
mkConnective Bottom s [] =
    BottomF . Kore.Bottom <$> (mkSort s)
mkConnective Not s [a] =
    fmap NotF $
        Kore.Not <$> mkSort s <*> toParsedPattern a
mkConnective And s [a, b] =
    fmap AndF $
        Kore.And <$> mkSort s <*> toParsedPattern a <*> toParsedPattern b
mkConnective Or s [a, b] =
    fmap OrF $
        Kore.Or <$> mkSort s <*> toParsedPattern a <*> toParsedPattern b
mkConnective Implies s [a, b] =
    fmap ImpliesF $
        Kore.Implies <$> mkSort s <*> toParsedPattern a <*> toParsedPattern b
mkConnective Iff s [a, b] =
    fmap IffF $
        Kore.Iff <$> mkSort s <*> toParsedPattern a <*> toParsedPattern b
-- fall-through cases because of wrong argument count
mkConnective conn _ as =
    Prelude.Left $ WrongArgCount (show conn) (length as)

mkPredicate ::
    Pred ->
    Sort ->
    Sort ->
    [KorePattern] ->
    Either JsonError (PatternF VariableName ParsedPattern)
mkPredicate Ceil s s2 [a] =
    fmap CeilF $
        Kore.Ceil <$> mkSort s <*> mkSort s2 <*> toParsedPattern a
mkPredicate Floor s s2 [a] =
    fmap FloorF $
        Kore.Floor <$> mkSort s <*> mkSort s2 <*> toParsedPattern a
mkPredicate Equals s s2 [a, b] =
    fmap EqualsF $
        Kore.Equals <$> mkSort s <*> mkSort s2 <*> toParsedPattern a <*> toParsedPattern b
mkPredicate In s s2 [a, b] =
    fmap InF $
        Kore.In <$> mkSort s <*> mkSort s2 <*> toParsedPattern a <*> toParsedPattern b
mkPredicate pred _ _ as =
    Prelude.Left $ WrongArgCount (show pred) (length as)

------------------------------------------------------------
-- writing

-- | Write a Pattern to a json byte string
encodePattern :: Kore.Pattern VariableName ann -> ByteString
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

fromParsedPattern :: Kore.Pattern VariableName ann -> KorePattern
fromParsedPattern _ = error "not implemented"
