{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}

{-# Options -Wno-partial-fields #-}

{- |
Copyright   : (c) Runtime Verification, 2019-2022
License     : BSD-3-Clause
-}
module Kore.Syntax.Json.Internal (
    -- export everything for debugging and testing only
    module Kore.Syntax.Json.Internal,
) where

import Data.Aeson as Json
import Data.Aeson.Types qualified as Json
import Data.Char (isAlpha, isDigit)
import Data.Foldable ()
import Data.Functor.Const (Const (..))
import Data.Functor.Foldable as Recursive (Recursive (..))
import Data.List (nub)
import Data.List.NonEmpty qualified as NE
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

------------------------------------------------------------
-- reading

-- see Parser.y
toParsedPattern :: KorePattern -> ParsedPattern
toParsedPattern = \case
    KJEVar n s ->
        (embedParsedPattern . VariableF . Const) $
            embedVar (SomeVariableNameElement . ElementVariableName) n s
    KJSVar n s ->
        (embedParsedPattern . VariableF . Const) $
            embedVar (SomeVariableNameSet . SetVariableName) n s
    KJApp n ss as ->
        (embedParsedPattern . ApplicationF) $
            Kore.Application (toSymbol n ss) (map toParsedPattern as)
    KJString t ->
        embedParsedPattern . StringLiteralF . Const $
            Kore.StringLiteral t
    KJTop s ->
        (embedParsedPattern . TopF) $
            Kore.Top (mkSort s)
    KJBottom s ->
        (embedParsedPattern . BottomF) $
            Kore.Bottom (mkSort s)
    KJNot s a ->
        (embedParsedPattern . NotF) $
            Kore.Not (mkSort s) (toParsedPattern a)
    KJAnd s a b ->
        (embedParsedPattern . AndF) $
            Kore.And (mkSort s) (toParsedPattern a) (toParsedPattern b)
    KJOr s a b ->
        (embedParsedPattern . OrF) $
            Kore.Or (mkSort s) (toParsedPattern a) (toParsedPattern b)
    KJImplies s a b ->
        (embedParsedPattern . ImpliesF) $
            Kore.Implies (mkSort s) (toParsedPattern a) (toParsedPattern b)
    KJIff s a b ->
        (embedParsedPattern . IffF) $
            Kore.Iff (mkSort s) (toParsedPattern a) (toParsedPattern b)
    KJForall{sort, var, varSort, arg} ->
        (embedParsedPattern . ForallF) $
            Kore.Forall
                (mkSort sort)
                (Variable (ElementVariableName (koreVar var)) $ mkSort varSort)
                (toParsedPattern arg)
    KJExists{sort, var, varSort, arg} ->
        (embedParsedPattern . ExistsF) $
            Kore.Exists
                (mkSort sort)
                (Variable (ElementVariableName (koreVar var)) $ mkSort varSort)
                (toParsedPattern arg)
    KJMu{var, varSort, arg} ->
        (embedParsedPattern . MuF) $
            Kore.Mu
                (Variable (SetVariableName (koreVar var)) $ mkSort varSort)
                (toParsedPattern arg)
    KJNu{var, varSort, arg} ->
        (embedParsedPattern . NuF) $
            Kore.Nu
                (Variable (SetVariableName (koreVar var)) $ mkSort varSort)
                (toParsedPattern arg)
    KJCeil{argSort, sort, arg} ->
        (embedParsedPattern . CeilF) $
            Kore.Ceil (mkSort argSort) (mkSort sort) (toParsedPattern arg)
    KJFloor{argSort, sort, arg} ->
        (embedParsedPattern . FloorF) $
            Kore.Floor (mkSort argSort) (mkSort sort) (toParsedPattern arg)
    KJEquals{argSort, sort, first, second} ->
        (embedParsedPattern . EqualsF) $
            Kore.Equals (mkSort argSort) (mkSort sort) (toParsedPattern first) (toParsedPattern second)
    KJIn{argSort, sort, first, second} ->
        (embedParsedPattern . InF) $
            Kore.In (mkSort argSort) (mkSort sort) (toParsedPattern first) (toParsedPattern second)
    KJNext{sort, dest} ->
        (embedParsedPattern . NextF) $
            Kore.Next (mkSort sort) (toParsedPattern dest)
    KJRewrites{sort, source, dest} ->
        (embedParsedPattern . RewritesF) $
            Kore.Rewrites (mkSort sort) (toParsedPattern source) $ toParsedPattern dest
    KJDV{sort, value} ->
        (embedParsedPattern . DomainValueF) $
            Kore.DomainValue (mkSort sort) (toParsedPattern (KJString value))
    KJMultiOr{assoc, sort, argss} ->
        withAssoc assoc (mkOr sort) $ NE.map toParsedPattern argss
    KJMultiApp{assoc, symbol, sorts, argss} ->
        withAssoc assoc (mkF symbol sorts) $ NE.map toParsedPattern argss
  where
    embedVar ::
        (VariableName -> SomeVariableName VariableName) ->
        Id ->
        Sort ->
        Variable (SomeVariableName VariableName)
    embedVar cons n s =
        Variable (mkVarName cons n) (mkSort s)

    mkVarName ::
        (VariableName -> SomeVariableName VariableName) ->
        Id ->
        (SomeVariableName VariableName)
    mkVarName embed = embed . koreVar

    toSymbol :: Id -> [Sort] -> Kore.SymbolOrAlias
    toSymbol n sorts = Kore.SymbolOrAlias (koreId n) $ map mkSort sorts

    withAssoc :: LeftRight -> (a -> a -> a) -> NE.NonEmpty a -> a
    withAssoc Left = foldl1
    withAssoc Right = foldr1

    mkOr :: Sort -> ParsedPattern -> ParsedPattern -> ParsedPattern
    mkOr s a b =
        embedParsedPattern . OrF $ Kore.Or (mkSort s) a b

    mkF :: Id -> [Sort] -> ParsedPattern -> ParsedPattern -> ParsedPattern
    mkF n sorts a b =
        embedParsedPattern . ApplicationF $ Kore.Application (toSymbol n sorts) [a, b]

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

mkSort :: Sort -> Kore.Sort
mkSort SortApp{name, args} =
    (Kore.SortActualSort . Kore.SortActual (koreId name)) $ map mkSort args
mkSort (SortVar name) =
    Kore.SortVariableSort $ Kore.SortVariable (koreId name)

------------------------------------------------------------
-- writing helper

fromPattern :: Kore.Pattern VariableName ann -> KorePattern
fromPattern = cata fromPatternF

fromPatternF :: CofreeF (Kore.PatternF VariableName) ann KorePattern -> KorePattern
fromPatternF (_ :< patt) = case patt of
    AndF Kore.And{andSort, andFirst, andSecond} ->
        KJAnd
            { sort = fromSort andSort
            , first = andFirst
            , second = andSecond
            }
    ApplicationF
        ( Kore.Application
                Kore.SymbolOrAlias{symbolOrAliasConstructor, symbolOrAliasParams}
                args
            ) ->
            KJApp
                { name = fromKoreId symbolOrAliasConstructor
                , sorts = map fromSort symbolOrAliasParams
                , args
                }
    BottomF Kore.Bottom{bottomSort} ->
        KJBottom{sort = fromSort bottomSort}
    CeilF Kore.Ceil{ceilOperandSort, ceilResultSort, ceilChild} ->
        KJCeil
            { argSort = fromSort ceilOperandSort
            , sort = fromSort ceilResultSort
            , arg = ceilChild
            }
    DomainValueF Kore.DomainValue{domainValueSort, domainValueChild = KJString value} ->
        KJDV
            { sort = fromSort domainValueSort
            , value
            }
    DomainValueF Kore.DomainValue{} ->
        error "Bad domain value"
    EqualsF Kore.Equals{equalsOperandSort, equalsResultSort, equalsFirst, equalsSecond} ->
        KJEquals
            { argSort = fromSort equalsOperandSort
            , sort = fromSort equalsResultSort
            , first = equalsFirst
            , second = equalsSecond
            }
    ExistsF Kore.Exists{existsSort, existsVariable, existsChild} ->
        KJExists
            { sort = fromSort existsSort
            , var = fromKoreVariableName $ Kore.unElementVariableName $ Kore.variableName existsVariable
            , varSort = fromSort $ Kore.variableSort existsVariable
            , arg = existsChild
            }
    FloorF Kore.Floor{floorOperandSort, floorResultSort, floorChild} ->
        KJFloor
            { argSort = fromSort floorOperandSort
            , sort = fromSort floorResultSort
            , arg = floorChild
            }
    ForallF Kore.Forall{forallSort, forallVariable, forallChild} ->
        KJForall
            { sort = fromSort forallSort
            , var = fromKoreVariableName $ unElementVariableName $ variableName forallVariable
            , varSort = fromSort $ variableSort forallVariable
            , arg = forallChild
            }
    IffF Kore.Iff{iffSort, iffFirst, iffSecond} ->
        KJIff
            { sort = fromSort iffSort
            , first = iffFirst
            , second = iffSecond
            }
    ImpliesF Kore.Implies{impliesSort, impliesFirst, impliesSecond} ->
        KJImplies
            { sort = fromSort impliesSort
            , first = impliesFirst
            , second = impliesSecond
            }
    InF Kore.In{inOperandSort, inResultSort, inContainedChild, inContainingChild} ->
        KJIn
            { argSort = fromSort inOperandSort
            , sort = fromSort inResultSort
            , first = inContainedChild
            , second = inContainingChild
            }
    MuF Kore.Mu{muVariable, muChild} ->
        KJMu
            { var = fromKoreVariableName $ unSetVariableName $ variableName muVariable
            , varSort = fromSort $ variableSort muVariable
            , arg = muChild
            }
    NextF Kore.Next{nextSort, nextChild} ->
        KJNext
            { sort = fromSort nextSort
            , dest = nextChild
            }
    NotF Kore.Not{notSort, notChild} ->
        KJNot
            { sort = fromSort notSort
            , arg = notChild
            }
    NuF Kore.Nu{nuVariable, nuChild} ->
        KJNu
            { var = fromKoreVariableName $ unSetVariableName $ variableName nuVariable
            , varSort = fromSort $ variableSort nuVariable
            , arg = nuChild
            }
    OrF Kore.Or{orSort, orFirst, orSecond} ->
        KJOr
            { sort = fromSort orSort
            , first = orFirst
            , second = orSecond
            }
    RewritesF Kore.Rewrites{rewritesSort, rewritesFirst, rewritesSecond} ->
        KJRewrites
            { sort = fromSort rewritesSort
            , source = rewritesFirst
            , dest = rewritesSecond
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
            SortApp
                { name = fromKoreId sortActualName
                , args = map fromSort sortActualSorts
                }
        Kore.SortVariableSort Kore.SortVariable{getSortVariable} ->
            SortVar . Id $ Kore.getId getSortVariable

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
