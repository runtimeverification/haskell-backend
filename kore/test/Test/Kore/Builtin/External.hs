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
import Kore.Internal.TermLike (InternalVariable, Key, DomainValue (..), InternalBytes (..), mapHead, Application (..), symbolApplication, StringLiteral (..))
import qualified Kore.Syntax.Pattern as Syntax
import qualified Kore.Validate as Validated
import Prelude.Kore

type FutuPattern variable t =
    Recursive.Base
        (Syntax.Pattern variable Attribute.Null)
        (Free (Recursive.Base (Syntax.Pattern variable Attribute.Null)) t)

{- | Externalize the 'Validated.Pattern' into a 'Syntax.Pattern'.

All builtins will be rendered using their concrete Kore syntax.

See also: 'asPattern'
-}
externalize ::
    forall variable.
    InternalVariable variable =>
    Validated.Pattern variable ->
    Syntax.Pattern variable Attribute.Null
externalize = Recursive.futu externalize1
  where
    externalize1 ::
        Validated.Pattern variable ->
        FutuPattern variable (Validated.Pattern variable)
    externalize1 termLike =
        -- TODO (thomas.tuegel): Make all these cases into classes.
        case termLikeF of
            Validated.AndF andF -> mkPurePattern Syntax.AndF andF
            Validated.ApplyAliasF applyAliasF -> mkApp $ mapHead Alias.toSymbolOrAlias applyAliasF
            Validated.ApplySymbolF applySymbolF -> mkApp $ mapHead Symbol.toSymbolOrAlias applySymbolF
            Validated.BottomF bottomF -> mkPurePattern Syntax.BottomF bottomF
            Validated.CeilF ceilF -> mkPurePattern Syntax.CeilF ceilF
            Validated.DomainValueF domainValueF -> mkPurePattern Syntax.DomainValueF domainValueF
            Validated.EqualsF equalsF -> mkPurePattern Syntax.EqualsF equalsF
            Validated.ExistsF existsF -> mkPurePattern Syntax.ExistsF existsF
            Validated.FloorF floorF -> mkPurePattern Syntax.FloorF floorF
            Validated.ForallF forallF -> mkPurePattern Syntax.ForallF forallF
            Validated.IffF iffF -> mkPurePattern Syntax.IffF iffF
            Validated.ImpliesF impliesF -> mkPurePattern Syntax.ImpliesF impliesF
            Validated.InF inF -> mkPurePattern Syntax.InF inF
            Validated.MuF muF -> mkPurePattern Syntax.MuF muF
            Validated.NextF nextF -> mkPurePattern Syntax.NextF nextF
            Validated.NotF notF -> mkPurePattern Syntax.NotF notF
            Validated.NuF nuF -> mkPurePattern Syntax.NuF nuF
            Validated.OrF orF -> mkPurePattern Syntax.OrF orF
            Validated.RewritesF rewritesF -> mkPurePattern Syntax.RewritesF rewritesF
            Validated.StringLiteralF stringLiteralF -> mkPurePattern Syntax.StringLiteralF stringLiteralF
            Validated.TopF topF -> mkPurePattern Syntax.TopF topF
            Validated.VariableF variableF -> mkPurePattern Syntax.VariableF variableF
            Validated.InhabitantF inhabitantF -> mkPurePattern Syntax.InhabitantF inhabitantF
            Validated.EndiannessF endiannessF ->
                mkApp $
                    mapHead Symbol.toSymbolOrAlias $
                        Endianness.toApplication $ getConst endiannessF
            Validated.SignednessF signednessF ->
                mkApp $
                    mapHead Symbol.toSymbolOrAlias $
                        Signedness.toApplication $ getConst signednessF
            -- Internals
            Validated.InternalBoolF (Const internalBool) -> externalizeBool internalBool
            Validated.InternalIntF (Const internalInt) -> externalizeInt internalInt
            Validated.InternalBytesF (Const internalBytes) -> externalizeBytes internalBytes
            Validated.InternalStringF (Const internalString) -> externalizeString internalString
            Validated.InternalListF internalList -> externalizeList internalList
            Validated.InternalSetF internalSet ->
                either externalize1 id $
                    externalizeSet internalSet
            Validated.InternalMapF internalMap ->
                either externalize1 id $
                    externalizeMap internalMap
            -- Inj
            Validated.InjF inj -> mkApp $ mapHead Symbol.toSymbolOrAlias (Inj.toApplication inj)
      where
        _ :< termLikeF = Recursive.project termLike
        mkPurePattern pattF = (Attribute.Null :<) . pattF . fmap Pure
        mkApp = mkPurePattern Syntax.ApplicationF

-- | Externalizes a 'Domain.InternalAc'
externalizeAc ::
    forall variable .
    UnitSymbol ->
    ConcatSymbol ->
    [FutuPattern variable (Validated.Pattern variable)] ->
    [FutuPattern variable (Validated.Pattern variable)] ->
    [Validated.Pattern variable] ->
    Either
        (Validated.Pattern variable)
        (FutuPattern variable (Validated.Pattern variable))
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
    forall variable.
    InternalVariable variable =>
    InternalMap Key (Validated.Pattern variable) ->
    Either
        (Validated.Pattern variable)
        (FutuPattern variable (Validated.Pattern variable))
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

    -- concreteElement ::
    --     (Key, Value NormalizedMap (Validated.Pattern variable)) ->
    --     FutuPattern variable (Validated.Pattern variable)
    concreteElement (key, mapValue) = undefined -- element (into key, mapValue)

    -- element ::
    --     (Validated.Pattern variable, Value NormalizedMap (Validated.Pattern variable)) ->
    --     FutuPattern variable (Validated.Pattern variable)
    element (key, MapValue value) = undefined
    --     (Attribute.Null :<) . Syntax.ApplicationF . fmap Pure
    --         . mapHead toSymbolOrAlias
    --         $ symbolApplication elementSymbol [undefined, undefined] -- [key, value]

    isEmptyMap (Validated.InternalMap_ InternalAc{builtinAcChild = wrappedChild}) =
        unwrapAc wrappedChild == emptyNormalizedAc
    isEmptyMap (Validated.App_ symbol _) = unitSymbol == symbol
    isEmptyMap _ = False

-- | Externalizes a 'Domain.InternalSet'
externalizeSet ::
    InternalVariable variable =>
    InternalSet Key (Validated.Pattern variable) ->
    Either
        (Validated.Pattern variable)
        (FutuPattern variable (Validated.Pattern variable))
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

    concreteElement (key, value) = undefined -- element (from @Key key, value)

    element (key, SetValue) = undefined
        -- (Attribute.Null :<) . Syntax.ApplicationF . fmap Pure
        --     . mapHead toSymbolOrAlias
        --     $ symbolApplication elementSymbol [key]

    isEmptySet (Validated.InternalSet_ InternalAc{builtinAcChild = wrappedChild}) =
        unwrapAc wrappedChild == emptyNormalizedAc
    isEmptySet (Validated.App_ symbol _) = unitSymbol == symbol
    isEmptySet _ = False

externalizeList ::
    InternalVariable variable =>
    InternalList (Validated.Pattern variable) ->
    FutuPattern variable (Validated.Pattern variable)
externalizeList builtin
    | Seq.null list = unit
    | otherwise = foldr1 concat' (element <$> list)
  where
    InternalList{internalListChild = list} = builtin
    InternalList{internalListUnit = unitSymbol} = builtin
    InternalList{internalListElement = elementSymbol} = builtin
    InternalList{internalListConcat = concatSymbol} = builtin

    unit = undefined
    --     (Attribute.Null :<) . Syntax.ApplicationF . fmap Pure
    --         . mapHead toSymbolOrAlias
    --         $ symbolApplication unitSymbol []
    element elem' = undefined
    --     (Attribute.Null :<) . Syntax.ApplicationF . fmap Pure
    --         . mapHead toSymbolOrAlias
    --         $ symbolApplication elementSymbol [elem']
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
    FutuPattern variable (Validated.Pattern variable)
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
    FutuPattern variable (Validated.Pattern variable)
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
    FutuPattern variable (Validated.Pattern variable)
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
    FutuPattern variable (Validated.Pattern variable)
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
