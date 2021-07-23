{- |
Copyright   : (c) Runtime Verification, 2021
License     : BSD-3-Clause
-}
module Test.Kore.Builtin.External (
    externalize,
) where

import Control.Monad.Free (Free (..))
import Data.Functor.Const (
    Const (..),
 )
import qualified Data.Functor.Foldable as Recursive
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import qualified Kore.Attribute.Null as Attribute
import Kore.Builtin.AssocComm.AssocComm
import qualified Kore.Builtin.Encoding as Encoding
import qualified Kore.Builtin.Endianness.Endianness as Endianness
import qualified Kore.Builtin.Signedness.Signedness as Signedness
import qualified Kore.Internal.Alias as Alias
import qualified Kore.Internal.Inj as Inj
import Kore.Internal.InternalBool
import Kore.Internal.InternalInt
import Kore.Internal.InternalList
import Kore.Internal.InternalMap
import Kore.Internal.InternalSet
import Kore.Internal.InternalString
import Kore.Internal.Symbol (
    toSymbolOrAlias,
 )
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike as TermLike
import qualified Kore.Syntax.Pattern as Syntax
import Prelude.Kore

type FutuPattern variable t =
    Recursive.Base
        (Syntax.Pattern variable Attribute.Null)
        (Free (Recursive.Base (Syntax.Pattern variable Attribute.Null)) t)

{- | Externalize the 'TermLike' into a 'Syntax.Pattern'.

All builtins will be rendered using their concrete Kore syntax.

See also: 'asPattern'
-}
externalize ::
    forall variable.
    InternalVariable variable =>
    TermLike variable ->
    Syntax.Pattern variable Attribute.Null
externalize = Recursive.futu externalize1
  where
    externalize1 ::
        TermLike variable -> FutuPattern variable (TermLike variable)
    externalize1 termLike =
        -- TODO (thomas.tuegel): Make all these cases into classes.
        case termLikeF of
            AndF andF -> mkPurePattern Syntax.AndF andF
            ApplyAliasF applyAliasF -> mkApp $ mapHead Alias.toSymbolOrAlias applyAliasF
            ApplySymbolF applySymbolF -> mkApp $ mapHead Symbol.toSymbolOrAlias applySymbolF
            BottomF bottomF -> mkPurePattern Syntax.BottomF bottomF
            CeilF ceilF -> mkPurePattern Syntax.CeilF ceilF
            DomainValueF domainValueF -> mkPurePattern Syntax.DomainValueF domainValueF
            EqualsF equalsF -> mkPurePattern Syntax.EqualsF equalsF
            ExistsF existsF -> mkPurePattern Syntax.ExistsF existsF
            FloorF floorF -> mkPurePattern Syntax.FloorF floorF
            ForallF forallF -> mkPurePattern Syntax.ForallF forallF
            IffF iffF -> mkPurePattern Syntax.IffF iffF
            ImpliesF impliesF -> mkPurePattern Syntax.ImpliesF impliesF
            InF inF -> mkPurePattern Syntax.InF inF
            MuF muF -> mkPurePattern Syntax.MuF muF
            NextF nextF -> mkPurePattern Syntax.NextF nextF
            NotF notF -> mkPurePattern Syntax.NotF notF
            NuF nuF -> mkPurePattern Syntax.NuF nuF
            OrF orF -> mkPurePattern Syntax.OrF orF
            RewritesF rewritesF -> mkPurePattern Syntax.RewritesF rewritesF
            StringLiteralF stringLiteralF -> mkPurePattern Syntax.StringLiteralF stringLiteralF
            TopF topF -> mkPurePattern Syntax.TopF topF
            VariableF variableF -> mkPurePattern Syntax.VariableF variableF
            InhabitantF inhabitantF -> mkPurePattern Syntax.InhabitantF inhabitantF
            EndiannessF endiannessF ->
                mkApp $
                    mapHead Symbol.toSymbolOrAlias $
                        Endianness.toApplication $ getConst endiannessF
            SignednessF signednessF ->
                mkApp $
                    mapHead Symbol.toSymbolOrAlias $
                        Signedness.toApplication $ getConst signednessF
            -- Internals
            InternalBoolF (Const internalBool) -> externalizeBool internalBool
            InternalIntF (Const internalInt) -> externalizeInt internalInt
            InternalBytesF (Const internalBytes) -> externalizeBytes internalBytes
            InternalStringF (Const internalString) -> externalizeString internalString
            InternalListF internalList -> externalizeList internalList
            InternalSetF internalSet ->
                either externalize1 id $
                    externalizeSet internalSet
            InternalMapF internalMap ->
                either externalize1 id $
                    externalizeMap internalMap
            -- Inj
            InjF inj -> mkApp $ mapHead Symbol.toSymbolOrAlias (Inj.toApplication inj)
      where
        _ :< termLikeF = Recursive.project termLike
        mkPurePattern pattF = (Attribute.Null :<) . pattF . fmap Pure
        mkApp = mkPurePattern Syntax.ApplicationF

-- | Externalizes a 'Domain.InternalAc'
externalizeAc ::
    UnitSymbol ->
    ConcatSymbol ->
    [FutuPattern variable (TermLike variable)] ->
    [FutuPattern variable (TermLike variable)] ->
    [TermLike variable] ->
    Either
        (TermLike variable)
        (FutuPattern variable (TermLike variable))
externalizeAc
    (UnitSymbol unitSymbol)
    (ConcatSymbol concatSymbol) = worker
      where
        worker [] [] [] = Right unit
          where
            unit =
                (Attribute.Null :<) . Syntax.ApplicationF $
                    Application (Symbol.toSymbolOrAlias unitSymbol) []
        worker concreteElements symbolicElements opaqueTerms =
            case foldr1 concat' operands of
                Free patternF -> Right patternF
                Pure termLike -> Left termLike
          where
            operands =
                map Free symbolicElements
                    <> map Pure opaqueTerms
                    <> map Free concreteElements
            concat' operand pat =
                Free $
                    (Attribute.Null :<) $
                        Syntax.ApplicationF $
                            Application
                                (Symbol.toSymbolOrAlias concatSymbol)
                                [operand, pat]

-- | Externalizes a 'Domain.InternalMap'
externalizeMap ::
    InternalVariable variable =>
    InternalMap Key (TermLike variable) ->
    Either
        (TermLike variable)
        (FutuPattern variable (TermLike variable))
externalizeMap builtin =
    externalizeAc
        (UnitSymbol unitSymbol)
        (ConcatSymbol concatSymbol)
        (map concreteElement (HashMap.toList concreteElements))
        (element . unwrapElement <$> elementsWithVariables)
        (filter (not . isEmptyMap) opaque)
  where
    InternalAc{builtinAcChild} = builtin
    InternalAc{builtinAcUnit = unitSymbol} = builtin
    InternalAc{builtinAcElement = elementSymbol} = builtin
    InternalAc{builtinAcConcat = concatSymbol} = builtin

    normalizedAc = unwrapAc builtinAcChild

    NormalizedAc{elementsWithVariables} = normalizedAc
    NormalizedAc{concreteElements} = normalizedAc
    NormalizedAc{opaque} = normalizedAc

    concreteElement (key, mapValue) = element (into key, mapValue)

    element (key, MapValue value) =
        (Attribute.Null :<) . Syntax.ApplicationF . fmap Pure
            . mapHead toSymbolOrAlias
            $ symbolApplication elementSymbol [key, value]

    isEmptyMap (InternalMap_ InternalAc{builtinAcChild = wrappedChild}) =
        unwrapAc wrappedChild == emptyNormalizedAc
    isEmptyMap (App_ symbol _) = unitSymbol == symbol
    isEmptyMap _ = False

-- | Externalizes a 'Domain.InternalSet'
externalizeSet ::
    InternalVariable variable =>
    InternalSet Key (TermLike variable) ->
    Either
        (TermLike variable)
        (FutuPattern variable (TermLike variable))
externalizeSet builtin =
    externalizeAc
        (UnitSymbol unitSymbol)
        (ConcatSymbol concatSymbol)
        (map concreteElement (HashMap.toList concreteElements))
        (element . unwrapElement <$> elementsWithVariables)
        (filter (not . isEmptySet) opaque)
  where
    InternalAc{builtinAcChild} = builtin
    InternalAc{builtinAcUnit = unitSymbol} = builtin
    InternalAc{builtinAcElement = elementSymbol} = builtin
    InternalAc{builtinAcConcat = concatSymbol} = builtin

    normalizedAc = unwrapAc builtinAcChild

    NormalizedAc{elementsWithVariables} = normalizedAc
    NormalizedAc{concreteElements} = normalizedAc
    NormalizedAc{opaque} = normalizedAc

    concreteElement (key, value) = element (from @Key key, value)

    element (key, SetValue) =
        (Attribute.Null :<) . Syntax.ApplicationF . fmap Pure
            . mapHead toSymbolOrAlias
            $ symbolApplication elementSymbol [key]

    isEmptySet (InternalSet_ InternalAc{builtinAcChild = wrappedChild}) =
        unwrapAc wrappedChild == emptyNormalizedAc
    isEmptySet (App_ symbol _) = unitSymbol == symbol
    isEmptySet _ = False

externalizeList ::
    InternalVariable variable =>
    InternalList (TermLike variable) ->
    FutuPattern variable (TermLike variable)
externalizeList builtin
    | Seq.null list = unit
    | otherwise = foldr1 concat' (element <$> list)
  where
    InternalList{internalListChild = list} = builtin
    InternalList{internalListUnit = unitSymbol} = builtin
    InternalList{internalListElement = elementSymbol} = builtin
    InternalList{internalListConcat = concatSymbol} = builtin

    unit =
        (Attribute.Null :<) . Syntax.ApplicationF . fmap Pure
            . mapHead toSymbolOrAlias
            $ symbolApplication unitSymbol []
    element elem' =
        (Attribute.Null :<) . Syntax.ApplicationF . fmap Pure
            . mapHead toSymbolOrAlias
            $ symbolApplication elementSymbol [elem']
    concat' list1 list2 =
        (Attribute.Null :<) $
            Syntax.ApplicationF $
                Application (toSymbolOrAlias concatSymbol) [Free list1, Free list2]

{- | Render a 'Bool' as a domain value pattern of the given sort.

  The result sort should be hooked to the builtin @Bool@ sort, but this is not
  checked.

  See also: 'sort'
-}
externalizeBool ::
    InternalBool ->
    FutuPattern variable (TermLike variable)
externalizeBool builtin =
    Attribute.Null
        :< Syntax.DomainValueF
            DomainValue
                { domainValueSort = internalBoolSort
                , domainValueChild
                }
  where
    InternalBool{internalBoolSort} = builtin
    InternalBool{internalBoolValue = bool} = builtin
    literal
        | bool = "true"
        | otherwise = "false"
    domainValueChild =
        Free . (:<) Attribute.Null . Syntax.StringLiteralF . Const $
            StringLiteral literal

{- | Render an 'String' as a domain value pattern of the given sort.

  The result sort should be hooked to the builtin @String@ sort, but this is not
  checked.

  See also: 'sort'
-}
externalizeString ::
    InternalString ->
    FutuPattern variable (TermLike variable)
externalizeString builtin =
    Attribute.Null
        :< Syntax.DomainValueF
            DomainValue
                { domainValueSort = internalStringSort
                , domainValueChild
                }
  where
    InternalString{internalStringSort} = builtin
    InternalString{internalStringValue} = builtin
    domainValueChild =
        Free . (:<) Attribute.Null . Syntax.StringLiteralF . Const $
            StringLiteral internalStringValue

{- | Render a 'Bytes' as a domain value pattern of the given sort.

The result sort should be hooked to the builtin @Bytes@ sort, but this is
not checked.

See also: 'sort'.
-}
externalizeBytes ::
    InternalBytes ->
    FutuPattern variable (TermLike variable)
externalizeBytes builtin =
    Attribute.Null
        :< Syntax.DomainValueF
            DomainValue
                { domainValueSort = internalBytesSort
                , domainValueChild
                }
  where
    InternalBytes{internalBytesSort} = builtin
    InternalBytes{internalBytesValue} = builtin
    domainValueChild =
        Free . (:<) Attribute.Null . Syntax.StringLiteralF . Const $
            StringLiteral (Encoding.decode8Bit internalBytesValue)

{- | Render an 'Integer' as a domain value pattern of the given sort.

  The result sort should be hooked to the builtin @Int@ sort, but this is not
  checked.

  See also: 'sort'
-}
externalizeInt ::
    InternalInt ->
    FutuPattern variable (TermLike variable)
externalizeInt builtin =
    Attribute.Null
        :< Syntax.DomainValueF
            DomainValue
                { domainValueSort = internalIntSort
                , domainValueChild
                }
  where
    InternalInt{internalIntSort} = builtin
    InternalInt{internalIntValue} = builtin
    domainValueChild =
        Free . (:<) Attribute.Null . Syntax.StringLiteralF . Const $
            StringLiteral (Text.pack $ show internalIntValue)
