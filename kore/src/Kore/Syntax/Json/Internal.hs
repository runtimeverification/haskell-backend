{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}

{-# Options -Wno-partial-fields #-}

module Kore.Syntax.Json.Internal (
    -- export everything for debugging and testing only
    module Kore.Syntax.Json.Internal,
) where

import Data.Aeson as Json
import Data.Aeson.Types qualified as Json
import Data.Char (isAlpha, isDigit, isPrint)
import Data.Either.Extra hiding (Left, Right)
import Data.Functor.Const (Const (..))
import Data.Functor.Foldable as Recursive (Recursive (..))
import Data.List (foldl1', nub)
import Data.Sup (Sup (..))
import Data.Text (Text)
import Data.Text qualified as T
import GHC.Generics -- FIXME switch to TH-generated Json instances
import Kore.Attribute.Attributes (ParsedPattern)
import Kore.Parser (embedParsedPattern)
import Kore.Syntax qualified as Kore
import Kore.Syntax.PatternF (PatternF (..))
import Kore.Syntax.Variable (
    ElementVariableName (..),
    SetVariableName (..),
    SomeVariableName (..),
    Variable (..),
    VariableName (..),
 )
import Prelude.Kore hiding (Left, Right)
import Prelude.Kore qualified as Prelude (Either (..))

{- | Json representation of Kore patterns as a Haskell type.
 Modeled after kore-syntax.md, merging some of the ML pattern
 productions. Cursorily checked to be consistent with Parser.y
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
        , resultSort :: Sort
        , arg :: KorePattern
        }
    | KJFloor
        { argSort :: Sort
        , resultSort :: Sort
        , arg :: KorePattern
        }
    | KJEquals
        { argSort :: Sort
        , resultSort :: Sort
        , first :: KorePattern
        , second :: KorePattern
        }
    | KJIn
        { argSort :: Sort
        , resultSort :: Sort
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
      KJDv
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
        "KJDv" -> "dv"
        'K' : 'J' : rest -> rest
        other -> other

----------------------------------------
-- Identifiers and lexical checks

newtype Id = Id Text
    deriving stock (Eq, Show, Generic)
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
        -- KJString txt ->
        --     reportErrors txt "string literal" checkStringChars
        -- for the time being, use standard Text (supports std
        -- Unicode) and do not check.
        KJForall{var = Id name} ->
            reportErrors name "quantifier variable" checkIdChars
        KJExists{var = Id name} ->
            reportErrors name "quantifier variable" checkIdChars
        KJMu{var = Id name} ->
            reportErrors name "fixpoint expression variable" checkSVarName
        KJNu{var = Id name} ->
            reportErrors name "fixpoint expression variable" checkSVarName
        KJDv{value = txt} ->
            reportErrors txt "domain value string" checkStringChars
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
 digits, _ or '. Set variables start with '@' followed by a basic
 identifier. Symbol variables _may_ start by \, followed by a basic
 identifier.
-}
checkIdChars :: Text -> [String] -- list of lexical errors
checkIdChars name
    | T.null name = ["Empty"]
checkIdChars name =
    ["Illegal initial character " <> show first | not $ isAlpha first]
    ++ [ "Contains illegal characters: " <> show (nub $ T.unpack illegalChars)
       | not $ T.null illegalChars
       ]
  where
    first = T.head name
    illegalChars = T.filter (not . isIdChar) $ T.tail name

isIdChar :: Char -> Bool
isIdChar c = isAlpha c || isDigit c || c `elem` ['_', '\'']

-- | Set variable names _have to_ start with `@`, followed by a valid identifier
checkSVarName :: Text -> [String]
checkSVarName name
    | T.null name = ["Empty"]
checkSVarName name =
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

{- | String literals may contain printable Ascii characters (0x20 -
 0x7e) except " and \, escape sequences \t, \n, \f, \r, \", \\, or
 Unicode escape sequences with 2, 4 or 8 hex: \xHH, \uHHHH, \UHHHHHHHH
-}
checkStringChars :: Text -> [String]
checkStringChars txt =
    [ "Contains non-printable characters: " <> (show . nub $ T.unpack nonPrintables)
    | not $ T.null nonPrintables
    ]
        ++ ["Contains invalid escape sequences: " <> showList badEscapes "" | not $ null badEscapes]
  where
    nonPrintables = T.filter (not . isPrint) txt
    badEscapes = reverse . fst $ T.foldl' collectEscapes ([], Normal) txt

-- Text fold function to collect invalid escape sequences in a string literal
data CollectState
    = Normal
    | Escape
    | UTF Int String
    | Bad Int String
    deriving stock (Show)

collectEscapes :: ([String], CollectState) -> Char -> ([String], CollectState)
-- normal mode
collectEscapes (acc, Normal) '\\' = (acc, Escape) -- enter escaped mode
collectEscapes (acc, Normal) _ = (acc, Normal) -- could check if printable here

-- escaping mode
collectEscapes (acc, Escape) 'x' = (acc, UTF 2 "x\\") -- enter UTF mode, expect 2 hex
collectEscapes (acc, Escape) 'u' = (acc, UTF 4 "u\\") -- enter UTF mode, expect 4 hex
collectEscapes (acc, Escape) 'U' = (acc, UTF 8 "U\\") -- enter UTF mode, expect 8 hex
collectEscapes (acc, Escape) c
    | c `elem` ['t', 'n', 'f', 'r', '\"', '\\'] -- good escape
        =
        (acc, Normal)
    | otherwise -- bad escape
        =
        (['\\', c] : acc, Normal)
-- UTF escape mode (n = remaining hex digits expected)
collectEscapes s@(acc, UTF n part) c
    | n > 8 || n < 0 = error $ "Illegal collect state" <> show s
    | n == 0 = collectEscapes (acc, Normal) c -- good UTF escape
    | c `elem` hexDigits = (acc, UTF (n -1) (c : part))
    | otherwise = (acc, Bad (n - 1) (c : part))
  where
    hexDigits = ['0' .. '9'] <> ['A' .. 'F'] <> ['a' .. 'f']

-- already bad, collect remaining expected hex digits no matter what they are)
collectEscapes s@(acc, Bad n part) c
    | n > 7 || n < 1 = error $ "Illegal collect state" <> show s
    | n == 1 = (reverse part : acc, Normal)
    | otherwise = (acc, Bad (n - 1) (c : part))

------------------------------------------------------------
data Sort
    = Sort
        { name :: Id
        , args :: [Sort]
        }
    | SortVariable
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

------------------------------------------------------------
-- reading

-- | Errors relating to the json codec, re-exported from API
data JsonError
    = -- | Problem reported by json parser
      ParseError String
    | -- | MultiOr/MultiApp require a non-empty argument list
      MissingArg String
    deriving stock (Eq, Show)

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
        pure . embedParsedPattern . StringLiteralF . Const $ Kore.StringLiteral t
    KJTop s ->
        fmap (embedParsedPattern . TopF) $
            Kore.Top <$> (mkSort s)
    KJBottom s ->
        fmap (embedParsedPattern . BottomF) $
            Kore.Bottom <$> (mkSort s)
    KJNot s a ->
        fmap (embedParsedPattern . NotF) $
            Kore.Not <$> mkSort s <*> toParsedPattern a
    KJAnd s a b ->
        fmap (embedParsedPattern . AndF) $
            Kore.And <$> mkSort s <*> toParsedPattern a <*> toParsedPattern b
    KJOr s a b ->
        fmap (embedParsedPattern . OrF) $
            Kore.Or <$> mkSort s <*> toParsedPattern a <*> toParsedPattern b
    KJImplies s a b ->
        fmap (embedParsedPattern . ImpliesF) $
            Kore.Implies <$> mkSort s <*> toParsedPattern a <*> toParsedPattern b
    KJIff s a b ->
        fmap (embedParsedPattern . IffF) $
            Kore.Iff <$> mkSort s <*> toParsedPattern a <*> toParsedPattern b
    KJForall{sort, var, varSort, arg} ->
        fmap (embedParsedPattern . ForallF) $
            Kore.Forall
                <$> mkSort sort
                <*> (Variable (ElementVariableName (koreVar var)) <$> mkSort varSort)
                <*> toParsedPattern arg
    KJExists{sort, var, varSort, arg} ->
        fmap (embedParsedPattern . ExistsF) $
            Kore.Exists
                <$> mkSort sort
                <*> (Variable (ElementVariableName (koreVar var)) <$> mkSort varSort)
                <*> toParsedPattern arg
    KJMu{var, varSort, arg} ->
        fmap (embedParsedPattern . MuF) $
            Kore.Mu
                <$> (Variable (SetVariableName (koreVar var)) <$> mkSort varSort)
                <*> toParsedPattern arg
    KJNu{var, varSort, arg} ->
        fmap (embedParsedPattern . NuF) $
            Kore.Nu
                <$> (Variable (SetVariableName (koreVar var)) <$> mkSort varSort)
                <*> toParsedPattern arg
    KJCeil s s2 a ->
        fmap (embedParsedPattern . CeilF) $
            Kore.Ceil <$> mkSort s <*> mkSort s2 <*> toParsedPattern a
    KJFloor s s2 a ->
        fmap (embedParsedPattern . FloorF) $
            Kore.Floor <$> mkSort s <*> mkSort s2 <*> toParsedPattern a
    KJEquals s s2 a b ->
        fmap (embedParsedPattern . EqualsF) $
            Kore.Equals <$> mkSort s <*> mkSort s2 <*> toParsedPattern a <*> toParsedPattern b
    KJIn s s2 a b ->
        fmap (embedParsedPattern . InF) $
            Kore.In <$> mkSort s <*> mkSort s2 <*> toParsedPattern a <*> toParsedPattern b
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
    KJDv{sort, value} ->
        fmap (embedParsedPattern . DomainValueF) $
            Kore.DomainValue
                <$> mkSort sort
                <*> toParsedPattern (KJString value)
    KJMultiOr{assoc, sort, args}
        | null args -> Prelude.Left $ MissingArg "MultiOr"
        | otherwise ->
            withAssoc assoc <$> mkOr sort <*> traverse toParsedPattern args
    KJMultiApp{assoc, symbol, sorts, args}
        | null args -> Prelude.Left $ MissingArg "MultiApp"
        | otherwise ->
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
    toSymbol n sorts = Kore.SymbolOrAlias (koreId n) <$> traverse mkSort sorts

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
koreVar (Id name) =
    -- TODO check well-formed (initial letter, char. set)
    VariableName (Kore.Id base Kore.AstLocationNone) suffix
  where
    baseName = T.dropWhileEnd isDigit name
    endDigits = T.takeWhileEnd isDigit name
    (zeros, actualNum) = T.break (/= '0') endDigits
    (base, suffix)
        | T.null endDigits = (baseName, Nothing)
        | T.null actualNum = (baseName <> T.init zeros, Just $ Element 0)
        | otherwise =
            (baseName <> zeros, Just $ Element (read $ T.unpack actualNum))

mkSort :: Sort -> Either JsonError Kore.Sort
mkSort Sort{name, args} =
    fmap (Kore.SortActualSort . Kore.SortActual (koreId name)) $
        mapM mkSort args
mkSort (SortVariable name) =
    pure . Kore.SortVariableSort $ Kore.SortVariable (koreId name)

------------------------------------------------------------
-- writing helper

fromPattern :: Kore.Pattern VariableName ann -> KorePattern
fromPattern pat =
    -- forget the annotation and recurse over the term-like PatternF
    let _ :< patF = Recursive.project pat
     in fromPatternF patF

fromPatternF :: Kore.PatternF VariableName (Kore.Pattern VariableName ann) -> KorePattern
fromPatternF = \case
    AndF Kore.And{andSort, andFirst, andSecond} ->
        KJAnd
            { sort = fromSort andSort
            , first = fromPattern andFirst
            , second = fromPattern andSecond
            }
    ApplicationF
        ( Kore.Application
                Kore.SymbolOrAlias{symbolOrAliasConstructor, symbolOrAliasParams}
                args
            ) ->
            KJApp
                { name = fromKoreId symbolOrAliasConstructor
                , sorts = map fromSort symbolOrAliasParams
                , args = map fromPattern args
                }
    BottomF Kore.Bottom{bottomSort} ->
        KJBottom{sort = fromSort bottomSort}
    CeilF Kore.Ceil{ceilOperandSort, ceilResultSort, ceilChild} ->
        KJCeil
            { argSort = fromSort ceilOperandSort
            , resultSort = fromSort ceilResultSort
            , arg = fromPattern ceilChild
            }
    DomainValueF Kore.DomainValue{domainValueSort, domainValueChild}
        | _ :< StringLiteralF (Const Kore.StringLiteral{getStringLiteral}) <-
            -- expected to contain a string literal value
            Recursive.project domainValueChild ->
            KJDv
                { sort = fromSort domainValueSort
                , value = getStringLiteral
                }
        | otherwise -> error "Bad domain value"
    EqualsF Kore.Equals{equalsOperandSort, equalsResultSort, equalsFirst, equalsSecond} ->
        KJEquals
            { argSort = fromSort equalsOperandSort
            , resultSort = fromSort equalsResultSort
            , first = fromPattern equalsFirst
            , second = fromPattern equalsSecond
            }
    ExistsF Kore.Exists{existsSort, existsVariable, existsChild} ->
        KJExists
            { sort = fromSort existsSort
            , var = fromKoreVariableName $ Kore.unElementVariableName $ Kore.variableName existsVariable
            , varSort = fromSort $ Kore.variableSort existsVariable
            , arg = fromPattern existsChild
            }
    FloorF Kore.Floor{floorOperandSort, floorResultSort, floorChild} ->
        KJFloor
            { argSort = fromSort floorOperandSort
            , resultSort = fromSort floorResultSort
            , arg = fromPattern floorChild
            }
    ForallF Kore.Forall{forallSort, forallVariable, forallChild} ->
        KJForall
            { sort = fromSort forallSort
            , var = fromKoreVariableName $ unElementVariableName $ variableName forallVariable
            , varSort = fromSort $ variableSort forallVariable
            , arg = fromPattern forallChild
            }
    IffF Kore.Iff{iffSort, iffFirst, iffSecond} ->
        KJIff
            { sort = fromSort iffSort
            , first = fromPattern iffFirst
            , second = fromPattern iffSecond
            }
    ImpliesF Kore.Implies{impliesSort, impliesFirst, impliesSecond} ->
        KJImplies
            { sort = fromSort impliesSort
            , first = fromPattern impliesFirst
            , second = fromPattern impliesSecond
            }
    InF Kore.In{inOperandSort, inResultSort, inContainedChild, inContainingChild} ->
        KJIn
            { argSort = fromSort inOperandSort
            , resultSort = fromSort inResultSort
            , first = fromPattern inContainedChild
            , second = fromPattern inContainingChild
            }
    MuF Kore.Mu{muVariable, muChild} ->
        KJMu
            { var = fromKoreVariableName $ unSetVariableName $ variableName muVariable
            , varSort = fromSort $ variableSort muVariable
            , arg = fromPattern muChild
            }
    NextF Kore.Next{nextSort, nextChild} ->
        KJNext
            { sort = fromSort nextSort
            , dest = fromPattern nextChild
            }
    NotF Kore.Not{notSort, notChild} ->
        KJNot
            { sort = fromSort notSort
            , arg = fromPattern notChild
            }
    NuF Kore.Nu{nuVariable, nuChild} ->
        KJNu
            { var = fromKoreVariableName $ unSetVariableName $ variableName nuVariable
            , varSort = fromSort $ variableSort nuVariable
            , arg = fromPattern nuChild
            }
    OrF Kore.Or{orSort, orFirst, orSecond} ->
        KJOr
            { sort = fromSort orSort
            , first = fromPattern orFirst
            , second = fromPattern orSecond
            }
    RewritesF Kore.Rewrites{rewritesSort, rewritesFirst, rewritesSecond} ->
        KJRewrites
            { sort = fromSort rewritesSort
            , source = fromPattern rewritesFirst
            , dest = fromPattern rewritesSecond
            }
    TopF Kore.Top{topSort} ->
        KJTop{sort = fromSort topSort}
    InhabitantF Kore.Inhabitant{} ->
        error "Found inhabitant, not representable in json"
    StringLiteralF (Const Kore.StringLiteral{getStringLiteral}) ->
        KJString getStringLiteral
    VariableF (Const Kore.Variable{variableName, variableSort})
        | Kore.SomeVariableNameElement (ElementVariableName evar) <- variableName ->
            KJEVar{name = fromKoreVariableName evar, sort}
        | Kore.SomeVariableNameSet (SetVariableName svar) <- variableName ->
            KJSVar{name = fromKoreVariableName svar, sort}
      where
        sort = fromSort variableSort
  where
    fromSort :: Kore.Sort -> Sort
    fromSort = \case
        Kore.SortActualSort Kore.SortActual{sortActualName, sortActualSorts} ->
            Sort
                { name = fromKoreId sortActualName
                , args = map fromSort sortActualSorts
                }
        Kore.SortVariableSort Kore.SortVariable{getSortVariable} ->
            SortVariable . Id $ Kore.getId getSortVariable

    fromKoreId :: Kore.Id -> Id
    fromKoreId =
        Id . Kore.getId -- forgetting the location
    fromKoreVariableName :: Kore.VariableName -> Id
    fromKoreVariableName VariableName{base, counter} =
        Id $
            Kore.getId base
                <> case counter of
                    Nothing -> ""
                    Just (Element n) -> T.pack $ show n
                    Just Sup -> error "Found Sup while converting variable name"
