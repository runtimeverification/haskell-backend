{-|
Module      : Data.Kore.MetaML.BuildersImpl
Description : Helper functions for 'Data.Kore.MetaML.Builder'
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Data.Kore.MetaML.BuildersImpl where

import           Data.Fix

import           Data.Kore.AST.Common
import           Data.Kore.MetaML.AST


newtype ChildSort = ChildSort (Sort Meta)
newtype ResultSort = ResultSort (Sort Meta)

{-|'fillCheckSorts' matches a list of sorts to a list of 'MetaPatternStub',
checking that the sorts are identical where possible, creating a pattern with
the provided sort otherwise.
-}
fillCheckSorts :: [Sort Meta] -> [MetaPatternStub] -> [CommonMetaPattern]
fillCheckSorts [] []         = []
fillCheckSorts [] _          = error "Not enough sorts!"
fillCheckSorts _ []          = error "Not enough patterns!"
fillCheckSorts (s:ss) (p:ps) = fillCheckSort s p : fillCheckSorts ss ps

{-|'fillCheckSorts' matches a sort to a 'MetaPatternStub', checking
that the pattern's sorts is identical if possible, creating a pattern with the
provided sort otherwise.
-}
fillCheckSort :: Sort Meta -> MetaPatternStub -> CommonMetaPattern
fillCheckSort
    desiredSort
    ( SortedPatternStub SortedPattern
        { sortedPatternPattern = p, sortedPatternSort = actualSort }
    )
  =
    if desiredSort /= actualSort
    then error
        (  "Unmatched sorts, expected:\n"
        ++ show desiredSort
        ++ "\nbut got:\n"
        ++ show actualSort
        ++ "\nfor pattern\n"
        ++ show p
        ++ "."
        )
    else Fix p
fillCheckSort desiredSort (UnsortedPatternStub p) =
    Fix (p desiredSort)

{-|'fillCheckPairSorts' takes two 'MetaPatternStub' objects, assumes that they
must have the same sort, and tries to build 'UnifiedPattern's from them if
possible, otherwise it returns functions that can build 'UnifiedPattern's.
-}
fillCheckPairSorts
    :: MetaPatternStub
    -> MetaPatternStub
    -> Either
        ( Sort Meta -> CommonMetaPattern
        , Sort Meta -> CommonMetaPattern
        )
        (Sort Meta, CommonMetaPattern, CommonMetaPattern)
fillCheckPairSorts (UnsortedPatternStub first) (UnsortedPatternStub second) =
    Left (Fix . first, Fix . second)
fillCheckPairSorts
    (UnsortedPatternStub first)
    ( SortedPatternStub SortedPattern
        { sortedPatternPattern = second, sortedPatternSort = s }
    )
  =
    Right
        ( s
        , Fix (first s)
        , Fix second
        )
fillCheckPairSorts
    ( SortedPatternStub SortedPattern
        { sortedPatternPattern = first, sortedPatternSort = s }
    )
    (UnsortedPatternStub second)
  =
    Right
        ( s
        , Fix first
        , Fix (second s)
        )
fillCheckPairSorts
    ( SortedPatternStub SortedPattern
        { sortedPatternPattern = p1, sortedPatternSort = actualSort1 }
    )
    ( SortedPatternStub SortedPattern
        { sortedPatternPattern = p2, sortedPatternSort = actualSort2 }
    )
  =
    if actualSort1 /= actualSort2
        then error
            (  "Unmatched sorts: "
            ++ show actualSort1
            ++ " and "
            ++ show actualSort2
            ++ "."
            )
        else
            Right
                ( actualSort1
                , Fix p1
                , Fix p2
                )

{-|'unaryPattern' is a helper for building 'MetaPatternStub's for unary
operators, like @\not@.
-}
unaryPattern
    :: (Sort Meta -> CommonMetaPattern -> PatternMetaType)
    -> MetaPatternStub
    -> MetaPatternStub
unaryPattern
    constructor
    ( SortedPatternStub SortedPattern
        { sortedPatternPattern = p, sortedPatternSort = s }
    )
  =
    SortedPatternStub SortedPattern
        { sortedPatternPattern = constructor s (Fix p)
        , sortedPatternSort    = s
        }
unaryPattern constructor (UnsortedPatternStub p) =
    UnsortedPatternStub (\sortS -> constructor sortS (Fix (p sortS)))

{-|'unarySortedPattern' is a helper for building 'MetaPatternStub's for unary
operators where the result sort is different from the operand sort, like \ceil.
-}
unarySortedPattern
    :: (ResultSort
        -> ChildSort
        -> CommonMetaPattern
        -> PatternMetaType)
    -> Maybe ChildSort
    -> MetaPatternStub
    -> MetaPatternStub
unarySortedPattern constructor maybeSort patternStub =
    UnsortedPatternStub
        (\sortS ->
            constructor
                (ResultSort sortS)
                (ChildSort childSort)
                (Fix $ sortedPatternPattern sortedPat)
        )
  where
    (childSort, SortedPatternStub sortedPat) = case (maybeSort, patternStub) of
        (Just (ChildSort sort), _) -> (sort, withSort sort patternStub)
        (Nothing, SortedPatternStub sp) -> (sortedPatternSort sp, patternStub)
        (_, UnsortedPatternStub usp) -> error
            (  "Could not find a sort for child pattern: "
            ++ show (usp dummyMetaSort)
            )

{-|'binaryPattern' is a helper for building 'MetaPatternStub's for binary
operators, like @\and@.
-}
binaryPattern
    :: (Sort Meta
        -> CommonMetaPattern
        -> CommonMetaPattern
        -> PatternMetaType)
    -> MetaPatternStub
    -> MetaPatternStub
    -> MetaPatternStub
binaryPattern constructor first second =
    case fillCheckPairSorts first second of
        Left (firstPattern, secondPattern) ->
            UnsortedPatternStub
                (\sortS ->
                    constructor sortS (firstPattern sortS) (secondPattern sortS)
                )
        Right (commonSort, firstPattern, secondPattern) ->
            SortedPatternStub SortedPattern
                { sortedPatternPattern =
                    constructor commonSort firstPattern secondPattern
                , sortedPatternSort    = commonSort
                }

{-|'binarySortedPattern' is a helper for building 'MetaPatternStub's for binary
operators where the result sort is different from the operand sort,
like \equals.
-}
binarySortedPattern
    :: (ResultSort
        -> ChildSort
        -> CommonMetaPattern
        -> CommonMetaPattern
        -> PatternMetaType)
    -> Maybe ChildSort
    -> MetaPatternStub
    -> MetaPatternStub
    -> MetaPatternStub
binarySortedPattern constructor maybeSort first second =
    case fillCheckPairSorts first second of
        Left (firstPattern, secondPattern) ->
            case maybeSort of
                Nothing ->
                    error
                        (  "Could not find a sort for equals children: "
                        ++ show (firstPattern dummyMetaSort)
                        ++ " and "
                        ++ show (secondPattern dummyMetaSort)
                        ++ "."
                        )
                Just childSort@(ChildSort s) ->
                    patternFromChildSort
                        (firstPattern s) (secondPattern s) childSort
        Right (commonSort, firstPattern, secondPattern) ->
            case maybeSort of
                Nothing ->
                    patternFromChildSort
                        firstPattern secondPattern (ChildSort commonSort)
                Just (ChildSort s) ->
                    if s == commonSort
                        then
                            patternFromChildSort
                                firstPattern
                                secondPattern
                                (ChildSort commonSort)
                        else
                            error
                                (  "Incompatible sorts for equals children: "
                                ++ show s
                                ++ " and "
                                ++ show commonSort
                                ++ "."
                                )
  where
    patternFromChildSort firstPattern secondPattern childSort =
        UnsortedPatternStub
            (\sortS ->
                constructor (ResultSort sortS) childSort
                    firstPattern
                    secondPattern
            )

equalsM_
    :: Maybe (Sort Meta)
    -> (MetaPatternStub -> MetaPatternStub -> MetaPatternStub)
equalsM_ s =
    binarySortedPattern
        (\(ResultSort resultSort)
            (ChildSort childSort)
            firstPattern
            secondPattern
          ->
            EqualsPattern Equals
                { equalsOperandSort = childSort
                , equalsResultSort  = resultSort
                , equalsFirst       = firstPattern
                , equalsSecond      = secondPattern
                }
        )
        (ChildSort <$> s)

inM_
    :: Maybe (Sort Meta)
    -> (MetaPatternStub -> MetaPatternStub -> MetaPatternStub)
inM_ s =
    binarySortedPattern
        (\(ResultSort resultSort)
            (ChildSort childSort)
            firstPattern
            secondPattern
          ->
            InPattern In
                { inOperandSort     = childSort
                , inResultSort      = resultSort
                , inContainedChild  = firstPattern
                , inContainingChild = secondPattern
                }
        )
        (ChildSort <$> s)

ceilM_ :: Maybe (Sort Meta) -> MetaPatternStub -> MetaPatternStub
ceilM_ s =
    unarySortedPattern
        (\(ResultSort resultSort)
            (ChildSort childSort)
            childPattern
          ->
            CeilPattern Ceil
                { ceilOperandSort = childSort
                , ceilResultSort  = resultSort
                , ceilChild       = childPattern
                }
        )
        (ChildSort <$> s)

floorM_ :: Maybe (Sort Meta) -> MetaPatternStub -> MetaPatternStub
floorM_ s =
    unarySortedPattern
        (\(ResultSort resultSort)
            (ChildSort childSort)
            childPattern
          ->
            FloorPattern Floor
                { floorOperandSort = childSort
                , floorResultSort  = resultSort
                , floorChild       = childPattern
                }
        )
        (ChildSort <$> s)
