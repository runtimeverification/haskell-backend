{-# LANGUAGE OverloadedStrings #-}

{-# Options -Wno-partial-fields #-}

{- |
Copyright   : (c) Runtime Verification, 2019-2022
License     : BSD-3-Clause
-}
module Kore.Syntax.Json.Internal (
    -- export everything for debugging and testing only
    module Kore.Syntax.Json.Internal,
    module Kore.Syntax.Json.Types,
) where

import Data.Char (isDigit)
import Data.Foldable ()
import Data.Functor.Const (Const (..))
import Data.Functor.Foldable as Recursive (Recursive (..))
import Data.List.NonEmpty qualified as NE
import Data.Sup (Sup (..))
import Data.Text qualified as T
import Kore.Attribute.Attributes (ParsedPattern)
import Kore.Parser (embedParsedPattern)
import Kore.Syntax qualified as Kore
import Kore.Syntax.Json.Types
import Kore.Syntax.PatternF (PatternF (..))
import Kore.Syntax.Variable (
    ElementVariableName (..),
    SetVariableName (..),
    SomeVariableName (..),
    Variable (..),
    VariableName (..),
 )
import Prelude.Kore hiding (Left, Right)

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
    KJAnd s as ->
        (embedParsedPattern . AndF) $
            Kore.And (mkSort s) (map toParsedPattern as)
    KJOr s as ->
        (embedParsedPattern . OrF) $
            Kore.Or (mkSort s) (map toParsedPattern as)
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
            Kore.Rewrites (mkSort sort) (toParsedPattern source) $
                toParsedPattern dest
    KJDV{sort, value} ->
        (embedParsedPattern . DomainValueF) $
            Kore.DomainValue (mkSort sort) (toParsedPattern (KJString value))
    KJMultiOr{assoc, sort, argss} ->
        withAssoc assoc (mkOr sort) $ NE.map toParsedPattern argss
    KJLeftAssoc{symbol, sorts, argss} ->
        foldl1 (mkF symbol sorts) $ NE.map toParsedPattern argss
    KJRightAssoc{symbol, sorts, argss} ->
        foldr1 (mkF symbol sorts) $ NE.map toParsedPattern argss
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
        embedParsedPattern . OrF $ Kore.Or (mkSort s) [a, b]

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
    AndF Kore.And{andSort, andChildren} ->
        KJAnd
            { sort = fromSort andSort
            , patterns = andChildren
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
    OrF Kore.Or{orSort, orChildren} ->
        KJOr
            { sort = fromSort orSort
            , patterns = orChildren
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
