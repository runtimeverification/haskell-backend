{-|
Copyright   : (c) Runtime Verification, 2021
License     : NCSA
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE Strict              #-}

module Kore.Step.Simplification.Unify
    ( matchAppHeads
    , matchAppInj
    , matchBools
    , matchBytesDifferent
    , matchDomainValue
    , matchEqualInjectiveHeadsAndEquals
    , matchFirstBottom
    , matchFirstElemVar
    , matchInjApp
    , matchInjs
    , matchInt
    , matchString
    , matchStringLiteral
    , matchUnDefined
    , matchUnifyBoolAnd
    , matchUnifyBoolNot
    , matchUnifyBoolOr
    , matchUnifyKequalsEq
    , matchUnifyIntEq
    , matchUnifyStringEq
    , matchUnifyEqualsEndianness
    , matchUnifyEqualsSignedness
    , matchUnifyNotInKeys
    , matchDomainValueAndConstructorErrors1
    , matchDomainValueAndConstructorErrors2
    , matchUnifyOverload1
    , matchUnifyOverload2
    , matchUnifyOverload3
    , matchUnifyOverload4
    , matchUnifyOverload5
    , matchUnifyOverload6
    , matchUnifyEqualsMap
    , matchUnifyEqualsSet
    , matchUnifyEqualsList
    , matchBoolAnd1
    , matchBoolAnd2
    , matchBoolAnd3
    , matchBoolAnd4
    , matchVariableFunctionAnd1
    , matchVariableFunctionAnd2
    , matchITE
    , matchExpandAlias
    , matchIsFunctionPatterns
    , Unification (..)
    , UnifyBoolOrArgs (..)
    , UnifyBoolNotArgs (..)
    , UnifyKequalsEqArgs (..)
    , UnifyIntEqArgs (..)
    , UnifyStringEqArgs (..)
    , UnifyEqualsEndiannessArgs (..)
    , UnifyEqualsSignednessArgs (..)
    , UnifyNotInKeysArgs (..)
    , UnifyOverload1Args (..)
    , UnifyOverload2Args (..)
    , UnifyOverload3Args (..)
    , UnifyOverload4Args (..)
    , UnifyOverload5Args (..)
    , UnifyOverload6Args (..)
    , UnifyEqualsList3Args (..)
    , UnifyEqualsList4Args (..)
    , UnifyEqualsList5Args (..)
    , UnifyMapEqualsArgs (..)
    , UnifyMapEqualsVarArgs (..)
    , UnifySetEqualsArgs (..)
    , UnifySetEqualsVarArgs (..)
    , UnifyExpandAliasArgs (..)
    ) where

import qualified Data.Functor.Foldable as Recursive
import qualified Data.List as List
import qualified Data.Map.Strict as M
import Data.Text
-- import Pretty (
--     Doc
--  )

import qualified Kore.Attribute.Symbol as Symbol
import qualified Kore.Builtin.AssociativeCommutative as Ac
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin
import Kore.Builtin.Endianness
import Kore.Builtin.EqTerm
import qualified Kore.Builtin.Int as Int
import Kore.Builtin.KEqual
import qualified Kore.Builtin.List.List as List
import qualified Kore.Builtin.Map as Map
import Kore.Builtin.Signedness
import qualified Kore.Builtin.String as String
import Kore.IndexedModule.MetadataTools
import Kore.Internal.InternalBool
import Kore.Internal.InternalInt
import Kore.Internal.InternalList
import Kore.Internal.InternalMap
import Kore.Internal.InternalSet
import Kore.Internal.InternalString
import Kore.Internal.Symbol
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable
import Kore.Step.Simplification.ExpandAlias
import Kore.Syntax.PatternF
    ( Const (..)
    )
import Kore.TopBottom
import Prelude.Kore

data Unification
    = UnifyInt !InternalInt !InternalInt
    | UnifyBool !InternalBool !InternalBool
    | UnifyString !InternalString !InternalString
    | UnifyDomainValue !Sort !(TermLike RewritingVariableName) !Sort !(TermLike RewritingVariableName)
    | UnifyStringLiteral !Text !Text
    | EqualsAndEquals
    | BytesDifferent !InternalBytes !InternalBytes
    | UnifyFirstBottom !Sort
    | VariableFunctionEquals !(ElementVariable RewritingVariableName)
    | EqualInjectiveHeadsAndEquals !Symbol ![TermLike RewritingVariableName] !Symbol ![TermLike RewritingVariableName]
    | MatchInjs !(Inj (TermLike RewritingVariableName)) !(Inj (TermLike RewritingVariableName))
    | MatchInjApp !Symbol
    | MatchAppInj !Symbol
    | MatchAppHeads !Symbol !Symbol
    | UnifyBoolAnd !(TermLike RewritingVariableName) !(TermLike RewritingVariableName)
    | UnifyBoolOr !UnifyBoolOrArgs
    | UnifyBoolNot !UnifyBoolNotArgs
    | UnifyKequalsEq !UnifyKequalsEqArgs
    | UnifyIntEq !UnifyIntEqArgs
    | UnifyStringEq !UnifyStringEqArgs
    | UnifyEqualsEndianness !UnifyEqualsEndiannessArgs
    | UnifyEqualsSignedness !UnifyEqualsSignednessArgs
    | UnifyNotInKeys !UnifyNotInKeysArgs
    | DomainValueAndConstructorErrors1
    | DomainValueAndConstructorErrors2
    | UnifyOverload1 !UnifyOverload1Args
    | UnifyOverload2 !UnifyOverload2Args
    | UnifyOverload3 !UnifyOverload3Args
    | UnifyOverload4 !UnifyOverload4Args
    | UnifyOverload5 !UnifyOverload5Args
    | UnifyOverload6 !UnifyOverload6Args
    | UnifyEqualsMap1 !UnifyMapEqualsArgs
    | UnifyEqualsMap2 !UnifyMapEqualsVarArgs
    | UnifyEqualsMap3 !UnifyMapEqualsVarArgs
    | UnifyMapBottom
    | UnifyEqualsSet1 !UnifySetEqualsArgs
    | UnifyEqualsSet2 !UnifySetEqualsVarArgs
    | UnifyEqualsSet3 !UnifySetEqualsVarArgs
    | UnifySetBottom
    | UnifyEqualsList1
    | UnifyEqualsList2
    | UnifyEqualsList3 !UnifyEqualsList3Args
    | UnifyEqualsList4 !UnifyEqualsList4Args
    | UnifyEqualsList5 !UnifyEqualsList5Args
    | UnifyBoolAnd1
    | UnifyBoolAnd2
    | UnifyBoolAnd3
    | UnifyBoolAnd4
    | UnifyVariableFunctionAnd1 !(ElementVariable RewritingVariableName)
    | UnifyVariableFunctionAnd2 !(ElementVariable RewritingVariableName)
    | UnifyIfThenElse !(IfThenElse (TermLike RewritingVariableName))
    | UnifyExpandAlias !UnifyExpandAliasArgs
    | UnifyIsFunctionPatterns

matchInt
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchInt first second
    | InternalInt_ int1 <- first
    , InternalInt_ int2 <- second
        = Just $ UnifyInt int1 int2
    | otherwise = Nothing
{-# INLINE matchInt #-}

matchBools
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchBools first second
    | InternalBool_ bool1 <- first
    , InternalBool_ bool2 <- second
        = Just $ UnifyBool bool1 bool2
    | otherwise = Nothing
{-# INLINE matchBools #-}

matchString
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchString first second
    | InternalString_ string1 <- first
    , InternalString_ string2 <- second
        = Just $ UnifyString string1 string2
    | otherwise = Nothing
{-# INLINE matchString #-}

matchDomainValue
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchDomainValue first second
    | DV_ sort1 val1 <- first
    , DV_ sort2 val2 <- second
        = Just $ UnifyDomainValue sort1 val1 sort2 val2
    | otherwise = Nothing
{-# INLINE matchDomainValue #-}

matchStringLiteral
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchStringLiteral first second
    | StringLiteral_ string1 <- first
    , StringLiteral_ string2 <- second
        = Just $ UnifyStringLiteral string1 string2
    | otherwise = Nothing
{-# INLINE matchStringLiteral #-}

matchUnDefined
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchUnDefined first second
    | first == second
        = Just EqualsAndEquals
    | otherwise = Nothing
{-# INLINE matchUnDefined #-}

matchBytesDifferent
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchBytesDifferent first second
    | _ :< InternalBytesF (Const bytesFirst) <- Recursive.project first
    , _ :< InternalBytesF (Const bytesSecond) <- Recursive.project second
        =  Just $ BytesDifferent bytesFirst bytesSecond
    | otherwise = Nothing
{-# INLINE matchBytesDifferent #-}

matchFirstBottom
    :: TermLike RewritingVariableName
    -> Maybe Unification
matchFirstBottom first
    | Bottom_ sort <- first
        = Just $ UnifyFirstBottom sort
    | otherwise = Nothing
{-# INLINE matchFirstBottom #-}

matchFirstElemVar
    :: TermLike RewritingVariableName
    -> Maybe Unification
matchFirstElemVar first
    | ElemVar_ var <- first
        = Just $ VariableFunctionEquals var
    | otherwise = Nothing
{-# INLINE matchFirstElemVar #-}

matchEqualInjectiveHeadsAndEquals
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchEqualInjectiveHeadsAndEquals first second
    | App_ firstHead firstChildren <- first
    , App_ secondHead secondChildren <- second
    , isInjective firstHead
    , isInjective secondHead
    , firstHead == secondHead --is one of the above redundant in light of this?
        = Just $ EqualInjectiveHeadsAndEquals firstHead firstChildren secondHead secondChildren
    | otherwise = Nothing
{-# INLINE matchEqualInjectiveHeadsAndEquals #-}

matchInjs
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchInjs first second
    | Inj_ inj1 <- first
    , Inj_ inj2 <- second
        = Just $ MatchInjs inj1 inj2
    | otherwise = Nothing
{-# INLINE matchInjs #-}

matchInjApp
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchInjApp first second
    | Inj_ _ <- first
    , App_ symbol _ <- second
        = Just $ MatchInjApp symbol
    | otherwise = Nothing
{-# INLINE matchInjApp #-}

matchAppInj
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchAppInj first second
    | App_ symbol _ <- first
    , Inj_ _ <- second
        = Just $ MatchAppInj symbol
    | otherwise = Nothing
{-# INLINE matchAppInj #-}

matchAppHeads
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchAppHeads first second
    | App_ firstHead _ <- first
    , App_ secondHead _ <- second
        = Just $ MatchAppHeads firstHead secondHead
    | otherwise = Nothing
{-# INLINE matchAppHeads #-}

matchUnifyBoolAnd
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchUnifyBoolAnd first second
    | Just value1 <- Bool.matchBool first
    , value1
    , Just Bool.BoolAnd { operand1, operand2 } <- Bool.matchBoolAnd second
    , isFunctionPattern second
        = Just $ UnifyBoolAnd operand1 operand2
    | otherwise = Nothing
{-# INLINE matchUnifyBoolAnd #-}

data UnifyBoolOrArgs = UnifyBoolOrArgs {
    otherTerm, operand1, operand2 :: !(TermLike RewritingVariableName)
}

matchUnifyBoolOr
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchUnifyBoolOr first second
    | Just value1 <- Bool.matchBool first
    , not value1
    , Just Bool.BoolOr { operand1, operand2 } <- Bool.matchBoolOr second
    , isFunctionPattern second
    = Just $ UnifyBoolOr $ UnifyBoolOrArgs first operand1 operand2
    | Just value2 <- Bool.matchBool second
    , not value2
    , Just Bool.BoolOr { operand1, operand2 } <- Bool.matchBoolOr first
    = Just $ UnifyBoolOr $ UnifyBoolOrArgs second operand1 operand2
    | otherwise = Nothing
{-# INLINE matchUnifyBoolOr #-}

data UnifyBoolNotArgs = UnifyBoolNotArgs {
    otherTerm, operand :: !(TermLike RewritingVariableName)
    , value :: Bool
}

matchUnifyBoolNot
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchUnifyBoolNot first second
    | Just Bool.BoolNot { operand } <- Bool.matchBoolNot first
    , isFunctionPattern first
    , Just value <- Bool.matchBool second
    = Just $ UnifyBoolNot $ UnifyBoolNotArgs second operand value
    | Just Bool.BoolNot { operand } <- Bool.matchBoolNot second
    , isFunctionPattern second
    , Just value <- Bool.matchBool first
    = Just $ UnifyBoolNot $ UnifyBoolNotArgs first operand value
    | otherwise = Nothing
{-# INLINE matchUnifyBoolNot #-}

data UnifyKequalsEqArgs = UnifyKequalsEqArgs {
    eqTerm :: EqTerm (TermLike RewritingVariableName)
    , otherTerm :: !(TermLike RewritingVariableName)
}

matchUnifyKequalsEq
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchUnifyKequalsEq first second
    | Just eqTerm <- matchKequalEq first
    , isFunctionPattern first
    = Just $ UnifyKequalsEq $ UnifyKequalsEqArgs eqTerm second
    | Just eqTerm <- matchKequalEq second
    , isFunctionPattern second
    = Just $ UnifyKequalsEq $ UnifyKequalsEqArgs eqTerm first
    | otherwise = Nothing

data UnifyIntEqArgs = UnifyIntEqArgs {
    eqTerm :: EqTerm (TermLike RewritingVariableName)
    , otherTerm :: !(TermLike RewritingVariableName)
}

matchUnifyIntEq
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchUnifyIntEq first second
    | Just eqTerm <- Int.matchIntEqual second
    , isFunctionPattern first
    = Just $ UnifyIntEq $ UnifyIntEqArgs eqTerm second
    | Just eqTerm <- Int.matchIntEqual first
    , isFunctionPattern second
    = Just $ UnifyIntEq $ UnifyIntEqArgs eqTerm first
    | otherwise = Nothing

data UnifyStringEqArgs = UnifyStringEqArgs {
    eqTerm :: EqTerm (TermLike RewritingVariableName)
    , otherTerm :: !(TermLike RewritingVariableName)
}

matchUnifyStringEq
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchUnifyStringEq first second
    | Just eqTerm <- String.matchStringEqual second
    , isFunctionPattern first
    = Just $ UnifyStringEq $ UnifyStringEqArgs eqTerm second
    | Just eqTerm <- String.matchStringEqual first
    , isFunctionPattern second
    = Just $ UnifyStringEq $ UnifyStringEqArgs eqTerm first
    | otherwise = Nothing

data UnifyEqualsEndiannessArgs = UnifyEqualsEndiannessArgs {
    end1, end2 :: Endianness
}

matchUnifyEqualsEndianness
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchUnifyEqualsEndianness first second
    | Endianness_ end1 <- first
    , Endianness_ end2 <- second
    = Just $ UnifyEqualsEndianness $ UnifyEqualsEndiannessArgs end1 end2
    | otherwise = Nothing

data UnifyEqualsSignednessArgs = UnifyEqualsSignednessArgs {
    sign1, sign2 :: Signedness
}

matchUnifyEqualsSignedness
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchUnifyEqualsSignedness first second
    | Signedness_ sign1 <- first
    , Signedness_ sign2 <- second
    = Just $ UnifyEqualsSignedness $ UnifyEqualsSignednessArgs sign1 sign2
    | otherwise = Nothing

data UnifyNotInKeysArgs = UnifyNotInKeysArgs {
    inKeys :: !(Map.InKeys (TermLike RewritingVariableName))
    , term, keyTerm, mapTerm :: !(TermLike RewritingVariableName)
}

matchUnifyNotInKeys
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchUnifyNotInKeys first second
    | Just boolValue <- Bool.matchBool first
    , not boolValue
    , Just inKeys@Map.InKeys { keyTerm, mapTerm } <- Map.matchInKeys first
    = Just $ UnifyNotInKeys $ UnifyNotInKeysArgs inKeys first keyTerm mapTerm
    | Just boolValue <- Bool.matchBool second
    , not boolValue
    , Just inKeys@Map.InKeys { keyTerm, mapTerm } <- Map.matchInKeys first
    = Just $ UnifyNotInKeys $ UnifyNotInKeysArgs inKeys second keyTerm mapTerm
    | otherwise = Nothing

matchDomainValueAndConstructorErrors1
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchDomainValueAndConstructorErrors1 first second
    | DV_ _ _ <- first
    , App_ secondHead _ <- second
    , isConstructor secondHead
    = Just DomainValueAndConstructorErrors1
    | otherwise = Nothing

matchDomainValueAndConstructorErrors2
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchDomainValueAndConstructorErrors2 first second
    | DV_ _ _ <- second
    , App_ firstHead _ <- first
    , isConstructor firstHead
    = Just DomainValueAndConstructorErrors1
    | otherwise = Nothing

mapSort :: Text
mapSort = "MAP.Map"

{- | Is the given sort hooked to the builtin Map sort?

Returns Nothing if the sort is unknown (i.e. the _PREDICATE sort).
Returns Just False if the sort is a variable.
-}
isMapSort :: SmtMetadataTools attrs -> Sort -> Maybe Bool
isMapSort = Builtin.isSort mapSort

{- | Verify that the sort is hooked to the builtin @Int@ sort.

  See also: 'sort', 'Builtin.verifySort'

 -}

data UnifyMapEqualsArgs = UnifyMapEqualsArgs {
    preElementsWithVariables1, preElementsWithVariables2 :: [Element NormalizedMap (TermLike RewritingVariableName)]
    , concreteElements1, concreteElements2 :: M.Map Key (Value NormalizedMap (TermLike RewritingVariableName))
    , opaque1, opaque2 :: [TermLike RewritingVariableName]
}

data UnifyMapEqualsVarArgs = UnifyMapEqualsVarArgs {
    preElementsWithVariables1, preElementsWithVariables2 :: [Element NormalizedMap (TermLike RewritingVariableName)]
    , concreteElements1, concreteElements2 :: M.Map Key (Value NormalizedMap (TermLike RewritingVariableName))
    , opaque1, opaque2 :: [TermLike RewritingVariableName]
    , var :: ElementVariable RewritingVariableName
}

unifyMapEqualsMatch ::
    Ac.TermNormalizedAc NormalizedMap RewritingVariableName ->
    Ac.TermNormalizedAc NormalizedMap RewritingVariableName ->
    Maybe Unification
unifyMapEqualsMatch
    norm1
    norm2 = case (opaqueDifference1, opaqueDifference2) of
        ([],[]) -> Just $ UnifyEqualsMap1 $ UnifyMapEqualsArgs preElementsWithVariables1 preElementsWithVariables2 concreteElements1 concreteElements2 opaque1 opaque2
        ([ElemVar_ v1], _) -> Just $ UnifyEqualsMap2 $ UnifyMapEqualsVarArgs preElementsWithVariables1 preElementsWithVariables2 concreteElements1 concreteElements2 opaque1 opaque2 v1
        (_, [ElemVar_ v2]) -> Just $ UnifyEqualsMap3 $ UnifyMapEqualsVarArgs preElementsWithVariables1 preElementsWithVariables2 concreteElements1 concreteElements2 opaque1 opaque2 v2
        _ -> Nothing

      where
        listToMap :: Ord a => [a] -> M.Map a Int
        listToMap = List.foldl' (\m k -> M.insertWith (+) k 1 m) M.empty
        mapToList :: M.Map a Int -> [a]
        mapToList =
            M.foldrWithKey
                (\key count' result -> List.replicate count' key ++ result)
                []

        NormalizedAc
            { elementsWithVariables = preElementsWithVariables1
            , concreteElements = concreteElements1
            , opaque = opaque1
            } =
                unwrapAc norm1
        NormalizedAc
            { elementsWithVariables = preElementsWithVariables2
            , concreteElements = concreteElements2
            , opaque = opaque2
            } =
                unwrapAc norm2

        --opaque1Map :: M.Map (TermLike RewritingVariableName) Int
        opaque1Map = listToMap opaque1
        opaque2Map = listToMap opaque2

        -- Duplicates must be kept in case any of the opaque terms turns out to be
        -- non-empty, in which case one of the terms is bottom, which
        -- means that the unification result is bottom.
        commonOpaqueMap = M.intersectionWith max opaque1Map opaque2Map

        commonOpaqueKeys = M.keysSet commonOpaqueMap

        opaqueDifference1 =
            mapToList (M.withoutKeys opaque1Map commonOpaqueKeys)
        opaqueDifference2 =
            mapToList (M.withoutKeys opaque2Map commonOpaqueKeys)

matchUnifyEqualsMap
    :: SmtMetadataTools Symbol.Symbol
    -> TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchUnifyEqualsMap tools first second
    | Just True <- isMapSort tools sort1
    = case unifyEquals0 first second of
        Just (norm1, norm2) ->
            let InternalAc{builtinAcChild = firstNormalized} =
                    norm1 in
            let InternalAc{builtinAcChild = secondNormalized} =
                    norm2 in
            unifyMapEqualsMatch firstNormalized secondNormalized
        Nothing -> return UnifyMapBottom
    | otherwise = Nothing

      where

        unifyEquals0 (InternalMap_ normalized1) (InternalMap_ normalized2)
          = return (normalized1, normalized2)
        unifyEquals0 first' second'
          = do
              firstDomain <- asDomain first'
              secondDomain <- asDomain second'
              unifyEquals0 firstDomain secondDomain

        sort1 = termLikeSort first

        asDomain ::
            TermLike RewritingVariableName ->
            Maybe (TermLike RewritingVariableName)
        asDomain patt =
            case normalizedOrBottom of
                Ac.Normalized normalized -> Just $
                    --tools <- Simplifier.askMetadataTools
                    Ac.asInternal tools sort1 normalized
                Ac.Bottom -> Nothing

          where
            normalizedOrBottom ::
                Ac.NormalizedOrBottom NormalizedMap RewritingVariableName
            normalizedOrBottom = Ac.toNormalized patt

data UnifySetEqualsArgs = UnifySetEqualsArgs {
    preElementsWithVariables1, preElementsWithVariables2 :: [Element NormalizedSet (TermLike RewritingVariableName)]
    , concreteElements1, concreteElements2 :: M.Map Key (Value NormalizedSet (TermLike RewritingVariableName))
    , opaque1, opaque2 :: [TermLike RewritingVariableName]
}

data UnifySetEqualsVarArgs = UnifySetEqualsVarArgs {
    preElementsWithVariables1, preElementsWithVariables2 :: [Element NormalizedSet (TermLike RewritingVariableName)]
    , concreteElements1, concreteElements2 :: M.Map Key (Value NormalizedSet (TermLike RewritingVariableName))
    , opaque1, opaque2 :: [TermLike RewritingVariableName]
    , var :: ElementVariable RewritingVariableName
}

unifySetEqualsMatch ::
    Ac.TermNormalizedAc NormalizedSet RewritingVariableName ->
    Ac.TermNormalizedAc NormalizedSet RewritingVariableName ->
    Maybe Unification
unifySetEqualsMatch
    norm1
    norm2 = case (opaqueDifference1, opaqueDifference2) of
        ([],[]) -> Just $ UnifyEqualsSet1 $ UnifySetEqualsArgs preElementsWithVariables1 preElementsWithVariables2 concreteElements1 concreteElements2 opaque1 opaque2
        ([ElemVar_ v1], _) -> Just $ UnifyEqualsSet2 $ UnifySetEqualsVarArgs preElementsWithVariables1 preElementsWithVariables2 concreteElements1 concreteElements2 opaque1 opaque2 v1
        (_, [ElemVar_ v2]) -> Just $ UnifyEqualsSet3 $ UnifySetEqualsVarArgs preElementsWithVariables1 preElementsWithVariables2 concreteElements1 concreteElements2 opaque1 opaque2 v2
        _ -> Nothing

      where
        listToMap :: Ord a => [a] -> M.Map a Int
        listToMap = List.foldl' (\m k -> M.insertWith (+) k 1 m) M.empty
        mapToList :: M.Map a Int -> [a]
        mapToList =
            M.foldrWithKey
                (\key count' result -> List.replicate count' key ++ result)
                []

        NormalizedAc
            { elementsWithVariables = preElementsWithVariables1
            , concreteElements = concreteElements1
            , opaque = opaque1
            } =
                unwrapAc norm1
        NormalizedAc
            { elementsWithVariables = preElementsWithVariables2
            , concreteElements = concreteElements2
            , opaque = opaque2
            } =
                unwrapAc norm2

        --opaque1Map :: M.Map (TermLike RewritingVariableName) Int
        opaque1Map = listToMap opaque1
        opaque2Map = listToMap opaque2

        -- Duplicates must be kept in case any of the opaque terms turns out to be
        -- non-empty, in which case one of the terms is bottom, which
        -- means that the unification result is bottom.
        commonOpaqueMap = M.intersectionWith max opaque1Map opaque2Map

        commonOpaqueKeys = M.keysSet commonOpaqueMap

        opaqueDifference1 =
            mapToList (M.withoutKeys opaque1Map commonOpaqueKeys)
        opaqueDifference2 =
            mapToList (M.withoutKeys opaque2Map commonOpaqueKeys)

-- | Builtin name of the @Set@ sort.
setSort :: Text
setSort = "SET.Set"

{- | Is the given sort hooked to the builtin Set sort?
Returns Nothing if the sort is unknown (i.e. the _PREDICATE sort).
Returns Just False if the sort is a variable.
-}
isSetSort :: SmtMetadataTools attrs -> Sort -> Maybe Bool
isSetSort = Builtin.isSort setSort

matchUnifyEqualsSet
    :: SmtMetadataTools Symbol.Symbol
    -> TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchUnifyEqualsSet tools first second
    | Just True <- isSetSort tools sort1
    = case unifyEquals0 first second of
        Just (norm1, norm2) ->
            let InternalAc{builtinAcChild = firstNormalized} =
                    norm1 in
            let InternalAc{builtinAcChild = secondNormalized} =
                    norm2 in
            unifySetEqualsMatch firstNormalized secondNormalized
        Nothing -> return UnifySetBottom 
    | otherwise = Nothing

      where
        
        unifyEquals0 (InternalSet_ normalized1) (InternalSet_ normalized2)
          = return (normalized1, normalized2)
        unifyEquals0 first' second'
          = do
              firstDomain <- asDomain first'
              secondDomain <- asDomain second'
              unifyEquals0 firstDomain secondDomain

        sort1 = termLikeSort first

        asDomain ::
            TermLike RewritingVariableName ->
            Maybe (TermLike RewritingVariableName)
        asDomain patt =
            case normalizedOrBottom of
                Ac.Normalized normalized -> Just $
                    --tools <- Simplifier.askMetadataTools
                    Ac.asInternal tools sort1 normalized
                Ac.Bottom -> Nothing
            
          where
            normalizedOrBottom ::
                Ac.NormalizedOrBottom NormalizedSet RewritingVariableName
            normalizedOrBottom = Ac.toNormalized patt

data UnifyEqualsList3Args = UnifyEqualsList3Args {
    symbol :: Symbol
    , args1, args2 :: [TermLike RewritingVariableName]
}

data UnifyEqualsList4Args = UnifyEqualsList4Args {
    builtin1, builtin2 :: InternalList (TermLike RewritingVariableName)
}

data UnifyEqualsList5Args = UnifyEqualsList5Args {
    builtin :: InternalList (TermLike RewritingVariableName)
    , args :: [TermLike RewritingVariableName]
}

matchUnifyEqualsList
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchUnifyEqualsList first second
    | ElemVar_ _ <- first
    = if isFunctionPattern second then Just UnifyEqualsList1 else Nothing
    | ElemVar_ _ <- second
    = if isFunctionPattern first then Just UnifyEqualsList2 else Nothing
    | App_ symbol1 args1 <- first
    , App_ symbol2 args2 <- second
    , List.isSymbolConcat symbol1
    , List.isSymbolConcat symbol2
    = Just $ UnifyEqualsList3 $ UnifyEqualsList3Args symbol2 args1 args2
    | InternalList_ builtIn1 <- first
    , InternalList_ builtIn2 <- second
    = Just $ UnifyEqualsList4 $ UnifyEqualsList4Args builtIn1 builtIn2
    | InternalList_ builtIn1 <- first
    , App_ symbol2 args2 <- second
    , List.isSymbolConcat symbol2 --
    = Just $ UnifyEqualsList5 $ UnifyEqualsList5Args builtIn1 args2
    | InternalList_ _ <- first
    = Nothing
    | InternalList_ _ <- second
    = matchUnifyEqualsList second first
    | otherwise
    = Nothing

data UnifyOverload1Args = UnifyOverload1Args {
    firstHead, secondHead :: Symbol
    , firstChildren :: [TermLike RewritingVariableName]
    , inj :: Inj (TermLike RewritingVariableName)
}

matchUnifyOverload1
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchUnifyOverload1 first second
    | Inj_ inj@Inj { injChild = App_ firstHead firstChildren } <- first
    , App_ secondHead _ <- second
    = Just $ UnifyOverload1 $ UnifyOverload1Args firstHead secondHead firstChildren inj
    | otherwise = Nothing

data UnifyOverload2Args = UnifyOverload2Args {
    firstHead, secondHead :: Symbol
    , secondChildren :: [TermLike RewritingVariableName]
    , inj :: Inj (TermLike RewritingVariableName)
}

matchUnifyOverload2
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchUnifyOverload2 first second
    | App_ firstHead _ <- first
    , Inj_ inj@Inj { injChild = App_ secondHead secondChildren } <- second
    = Just $ UnifyOverload2 $ UnifyOverload2Args firstHead secondHead secondChildren inj
    | otherwise = Nothing

data UnifyOverload3Args = UnifyOverload3Args {
    firstHead, secondHead :: Symbol
    , firstChildren, secondChildren :: [TermLike RewritingVariableName]
    , inj :: Inj (TermLike RewritingVariableName)
}

matchUnifyOverload3
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchUnifyOverload3 first second
    | Inj_ inj@Inj { injChild = App_ firstHead firstChildren } <- first
    , Inj_ inj'@Inj { injChild = App_ secondHead secondChildren } <- second
    , injFrom inj /= injFrom inj'
    = Just $ UnifyOverload3 $ UnifyOverload3Args firstHead secondHead firstChildren secondChildren inj
    | otherwise = Nothing

data UnifyOverload4Args = UnifyOverload4Args {
    firstHead :: Symbol
    , secondVar :: ElementVariable RewritingVariableName
    , inj :: Inj (TermLike RewritingVariableName)
}

matchUnifyOverload4
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchUnifyOverload4 first second
    | App_ firstHead _ <- first
    , Inj_ inj@Inj { injChild = ElemVar_ secondVar } <- second
    = Just $ UnifyOverload4 $ UnifyOverload4Args firstHead secondVar inj
    | App_ secondHead _ <- second
    , Inj_ inj@Inj { injChild = ElemVar_ firstVar } <- first
    = Just $ UnifyOverload4 $ UnifyOverload4Args secondHead firstVar inj
    | otherwise = Nothing

data UnifyOverload5Args = UnifyOverload5Args {
    firstTerm :: TermLike RewritingVariableName
    , firstHead :: Symbol
    , firstChildren :: [TermLike RewritingVariableName]
    , secondVar :: ElementVariable RewritingVariableName
    , inj :: Inj (TermLike RewritingVariableName)
}

matchUnifyOverload5
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchUnifyOverload5 first second
    | Inj_ Inj { injChild = firstTerm@(App_ firstHead firstChildren) } <- first
    , Inj_ inj@Inj { injChild = ElemVar_ secondVar } <- second
    = Just $ UnifyOverload5 $ UnifyOverload5Args firstTerm firstHead firstChildren secondVar inj
    | Inj_ Inj { injChild = secondTerm@(App_ secondHead secondChildren) } <- second
    , Inj_ inj@Inj { injChild = ElemVar_ firstVar } <- first
    = Just $ UnifyOverload5 $ UnifyOverload5Args secondTerm secondHead secondChildren firstVar inj
    | otherwise = Nothing

data UnifyOverload6Args = UnifyOverload6Args {
    firstHead :: Symbol
    , injChild :: TermLike RewritingVariableName
}

matchUnifyOverload6
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchUnifyOverload6 first second
    | App_ firstHead _ <- first
    , Inj_ Inj { injChild } <- second
    = Just $ UnifyOverload6 $ UnifyOverload6Args firstHead injChild
    | otherwise = Nothing

matchBoolAnd1
    :: TermLike RewritingVariableName
    -> Maybe Unification
matchBoolAnd1 first
    | isBottom first
    = Just UnifyBoolAnd1
    | otherwise
    = Nothing

matchBoolAnd2
    :: TermLike RewritingVariableName
    -> Maybe Unification
matchBoolAnd2 first
    | isTop first
    = Just UnifyBoolAnd2
    | otherwise
    = Nothing

matchBoolAnd3
    :: TermLike RewritingVariableName
    -> Maybe Unification
matchBoolAnd3 second
    | isBottom second
    = Just UnifyBoolAnd3
    | otherwise
    = Nothing

matchBoolAnd4
    :: TermLike RewritingVariableName
    -> Maybe Unification
matchBoolAnd4 second
    | isTop second
    = Just UnifyBoolAnd4
    | otherwise
    = Nothing

matchVariableFunctionAnd1
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchVariableFunctionAnd1 first second
    | ElemVar_ v <- first
    , ElemVar_ _ <- second
    = Just $ UnifyVariableFunctionAnd1 v
    | otherwise
    = Nothing

matchVariableFunctionAnd2
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchVariableFunctionAnd2 first second
    | ElemVar_ v <- first
    , isFunctionPattern second
    = Just $ UnifyVariableFunctionAnd2 v
    | otherwise
    = Nothing

matchITE
    :: TermLike RewritingVariableName
    -> Maybe Unification
matchITE first
     | Just ifThenElse <- matchIfThenElse first
     = Just $ UnifyIfThenElse ifThenElse
     | otherwise
     = Nothing

data UnifyExpandAliasArgs = UnifyExpandAliasArgs {
    term1, term2 :: !(TermLike RewritingVariableName)
}

matchExpandAlias
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchExpandAlias first second
    | Just term1 <- expandSingleAlias first
    , Just term2 <- expandSingleAlias second
    = Just $ UnifyExpandAlias $ UnifyExpandAliasArgs term1 term2
    | otherwise
    = Nothing

-- | isFunctionPattern first, isFunctionPattern second =

matchIsFunctionPatterns
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe Unification
matchIsFunctionPatterns first second
    | isFunctionPattern first
    , isFunctionPattern second
    = Just UnifyIsFunctionPatterns
    | otherwise
    = Nothing