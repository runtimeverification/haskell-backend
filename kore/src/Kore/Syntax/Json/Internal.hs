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

import Data.ByteString.Short qualified as ByteString
import Data.Char (isDigit)
import Data.Foldable ()
import Data.Functor.Const (Const (..))
import Data.Functor.Foldable as Recursive (Recursive (..))
import Data.HashMap.Lazy qualified as HashMap
import Data.List.NonEmpty qualified as NE
import Data.Sup (Sup (..))
import Data.Text qualified as T
import Data.Text qualified as Text
import Kore.Attribute.Attributes (ParsedPattern)
import Kore.Builtin.Encoding qualified as Encoding
import Kore.Builtin.Endianness.Endianness qualified as Endianness
import Kore.Builtin.Signedness.Signedness qualified as Signedness
import Kore.Internal.Alias qualified as Kore
import Kore.Internal.Inj qualified as Inj
import Kore.Internal.InternalBool (InternalBool (..))
import Kore.Internal.InternalInt (InternalInt (..))
import Kore.Internal.InternalList (InternalList (..))
import Kore.Internal.InternalMap (
    AcWrapper,
    InternalAc (..),
    NormalizedAc (..),
    concreteElementToApplicationArgs,
    elementToApplicationArgs,
    unwrapAc,
 )
import Kore.Internal.InternalString (InternalString (..))
import Kore.Internal.Symbol qualified as Kore
import Kore.Internal.TermLike (InternalBytes (..), Key)
import Kore.Internal.TermLike qualified as TermLike
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

fromTermLike ::
    TermLike.TermLike VariableName ->
    KorePattern
fromTermLike = cata go
  where
    go ::
        CofreeF
            (TermLike.TermLikeF VariableName)
            attrs
            KorePattern ->
        KorePattern
    go (_ :< trmLikePat) = case trmLikePat of
        TermLike.AndF Kore.And{andSort, andFirst, andSecond} ->
            KJAnd
                { sort = fromSort andSort
                , first = andFirst
                , second = andSecond
                }
        TermLike.ApplySymbolF
            ( Kore.Application
                    Kore.Symbol{symbolConstructor, symbolParams}
                    args
                ) ->
                KJApp
                    { name = fromKoreId symbolConstructor
                    , sorts = map fromSort symbolParams
                    , args
                    }
        TermLike.ApplyAliasF
            ( Kore.Application
                    Kore.Alias{aliasConstructor, aliasParams}
                    args
                ) ->
                KJApp
                    { name = fromKoreId aliasConstructor
                    , sorts = map fromSort aliasParams
                    , args
                    }
        TermLike.BottomF Kore.Bottom{bottomSort} ->
            KJBottom{sort = fromSort bottomSort}
        TermLike.CeilF Kore.Ceil{ceilOperandSort, ceilResultSort, ceilChild} ->
            KJCeil
                { argSort = fromSort ceilOperandSort
                , sort = fromSort ceilResultSort
                , arg = ceilChild
                }
        TermLike.DomainValueF Kore.DomainValue{domainValueSort, domainValueChild = KJString value} ->
            KJDV
                { sort = fromSort domainValueSort
                , value
                }
        TermLike.DomainValueF Kore.DomainValue{} ->
            error "Bad domain value"
        TermLike.EqualsF Kore.Equals{equalsOperandSort, equalsResultSort, equalsFirst, equalsSecond} ->
            KJEquals
                { argSort = fromSort equalsOperandSort
                , sort = fromSort equalsResultSort
                , first = equalsFirst
                , second = equalsSecond
                }
        TermLike.ExistsF Kore.Exists{existsSort, existsVariable, existsChild} ->
            KJExists
                { sort = fromSort existsSort
                , var = fromKoreVariableName $ Kore.unElementVariableName $ Kore.variableName existsVariable
                , varSort = fromSort $ Kore.variableSort existsVariable
                , arg = existsChild
                }
        TermLike.FloorF Kore.Floor{floorOperandSort, floorResultSort, floorChild} ->
            KJFloor
                { argSort = fromSort floorOperandSort
                , sort = fromSort floorResultSort
                , arg = floorChild
                }
        TermLike.ForallF Kore.Forall{forallSort, forallVariable, forallChild} ->
            KJForall
                { sort = fromSort forallSort
                , var = fromKoreVariableName $ unElementVariableName $ variableName forallVariable
                , varSort = fromSort $ variableSort forallVariable
                , arg = forallChild
                }
        TermLike.IffF Kore.Iff{iffSort, iffFirst, iffSecond} ->
            KJIff
                { sort = fromSort iffSort
                , first = iffFirst
                , second = iffSecond
                }
        TermLike.ImpliesF Kore.Implies{impliesSort, impliesFirst, impliesSecond} ->
            KJImplies
                { sort = fromSort impliesSort
                , first = impliesFirst
                , second = impliesSecond
                }
        TermLike.InF Kore.In{inOperandSort, inResultSort, inContainedChild, inContainingChild} ->
            KJIn
                { argSort = fromSort inOperandSort
                , sort = fromSort inResultSort
                , first = inContainedChild
                , second = inContainingChild
                }
        TermLike.MuF Kore.Mu{muVariable, muChild} ->
            KJMu
                { var = fromKoreVariableName $ unSetVariableName $ variableName muVariable
                , varSort = fromSort $ variableSort muVariable
                , arg = muChild
                }
        TermLike.NextF Kore.Next{nextSort, nextChild} ->
            KJNext
                { sort = fromSort nextSort
                , dest = nextChild
                }
        TermLike.NotF Kore.Not{notSort, notChild} ->
            KJNot
                { sort = fromSort notSort
                , arg = notChild
                }
        TermLike.NuF Kore.Nu{nuVariable, nuChild} ->
            KJNu
                { var = fromKoreVariableName $ unSetVariableName $ variableName nuVariable
                , varSort = fromSort $ variableSort nuVariable
                , arg = nuChild
                }
        TermLike.OrF Kore.Or{orSort, orFirst, orSecond} ->
            KJOr
                { sort = fromSort orSort
                , first = orFirst
                , second = orSecond
                }
        TermLike.RewritesF Kore.Rewrites{rewritesSort, rewritesFirst, rewritesSecond} ->
            KJRewrites
                { sort = fromSort rewritesSort
                , source = rewritesFirst
                , dest = rewritesSecond
                }
        TermLike.TopF Kore.Top{topSort} ->
            KJTop{sort = fromSort topSort}
        TermLike.InhabitantF Kore.Inhabitant{} ->
            error "Found inhabitant, not representable in json"
        TermLike.StringLiteralF (Const Kore.StringLiteral{getStringLiteral}) ->
            KJString getStringLiteral
        TermLike.VariableF (Const Kore.Variable{variableName, variableSort})
            | Kore.SomeVariableNameElement (ElementVariableName evar) <- variableName ->
                KJEVar{name = fromKoreVariableName evar, sort}
            | Kore.SomeVariableNameSet (SetVariableName svar) <- variableName ->
                KJSVar{name = fromKoreVariableName svar, sort}
          where
            sort = fromSort variableSort
        TermLike.EndiannessF (Const endianness)
            | Kore.Symbol{symbolConstructor, symbolParams} <- Endianness.toSymbol endianness ->
                KJApp
                    { name = fromKoreId symbolConstructor
                    , sorts = map fromSort symbolParams
                    , args = []
                    }
        TermLike.SignednessF (Const signedness)
            | Kore.Symbol{symbolConstructor, symbolParams} <- Signedness.toSymbol signedness ->
                undefined
                    KJApp
                        { name = fromKoreId symbolConstructor
                        , sorts = map fromSort symbolParams
                        , args = []
                        }
        TermLike.InjF inj
            | ( Kore.Application
                    Kore.Symbol{symbolConstructor, symbolParams}
                    args
                ) <-
                Inj.toApplication inj ->
                KJApp
                    { name = fromKoreId symbolConstructor
                    , sorts = map fromSort symbolParams
                    , args
                    }
        TermLike.InternalBoolF (Const (InternalBool boolSort boolValue)) ->
            encodeInternalValue boolSort $
                if boolValue then "true" else "false"
        TermLike.InternalBytesF (Const (InternalBytes bytesSort bytesValue)) ->
            encodeInternalValue bytesSort $
                Encoding.decode8Bit $
                    ByteString.fromShort bytesValue
        TermLike.InternalIntF (Const (InternalInt intSort intValue)) ->
            encodeInternalValue intSort $
                Text.pack $
                    show intValue
        TermLike.InternalStringF (Const (InternalString stringSort stringValue)) ->
            encodeInternalValue stringSort stringValue
        TermLike.InternalListF internalList -> encodeInternalList internalList
        TermLike.InternalMapF internalMap -> encodeInternalAc internalMap
        TermLike.InternalSetF internalSet -> encodeInternalAc internalSet
      where
        encodeInternalValue domainValueSort value =
            KJDV
                { sort = fromSort domainValueSort
                , value
                }

        -- The encoded lists and ac types are all of the following form:
        -- If the structure has no elements, we simply get the application of the unit symbol with no arguments
        -- If the structure has exactly one child, we just get the child.
        -- This child will be an application of internalElement symbol to its arguments
        -- For multiple children we will get a \right-assoc{concatSymbol}(x1,...x_n)
        foldApplication Kore.Symbol{symbolConstructor = unitSymbolConstructor, symbolParams = unitSymbolParams} Kore.Symbol{symbolConstructor = concatSymbolConstructor, symbolParams = concatSymbolParams} = foldAux
          where
            foldAux = \case
                [] ->
                    KJApp
                        { name = fromKoreId unitSymbolConstructor
                        , sorts = map fromSort unitSymbolParams
                        , args = []
                        }
                [x] -> x
                (x : xs) ->
                    KJRightAssoc
                        { symbol = fromKoreId concatSymbolConstructor
                        , sorts = map fromSort concatSymbolParams
                        , argss = x :| xs
                        }

        encodeInternalList
            InternalList
                { internalListUnit
                , internalListConcat
                , internalListElement =
                    Kore.Symbol{symbolConstructor = elementSymbolConstructor, symbolParams = elementSymbolParams}
                , internalListChild
                } =
                foldApplication internalListUnit internalListConcat children
              where
                encodeListElement e =
                    KJApp
                        { name = fromKoreId elementSymbolConstructor
                        , sorts = map fromSort elementSymbolParams
                        , args = [e]
                        }

                children = map encodeListElement $ toList internalListChild

        encodeInternalAc ::
            forall normalized.
            AcWrapper normalized =>
            InternalAc Key normalized KorePattern ->
            KorePattern
        encodeInternalAc
            InternalAc
                { builtinAcUnit
                , builtinAcConcat
                , builtinAcElement =
                    Kore.Symbol{symbolConstructor = elementSymbolConstructor, symbolParams = elementSymbolParams}
                , builtinAcChild
                } =
                foldApplication builtinAcUnit builtinAcConcat children
              where
                NormalizedAc{elementsWithVariables, concreteElements, opaque} = unwrapAc builtinAcChild

                encodeAcElement args =
                    KJApp
                        { name = fromKoreId elementSymbolConstructor
                        , sorts = map fromSort elementSymbolParams
                        , args
                        }

                encodedElementsWithVariables =
                    map
                        ( encodeAcElement
                            . elementToApplicationArgs
                        )
                        elementsWithVariables

                encodedConcreteElements =
                    map
                        ( \(k, v) ->
                            encodeAcElement $
                                encodeKey k : concreteElementToApplicationArgs v
                        )
                        $ HashMap.toList concreteElements

                encodeKey = fromTermLike . from

                children =
                    encodedElementsWithVariables ++ encodedConcreteElements ++ opaque
