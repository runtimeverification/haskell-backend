{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Kore.Step.Simplification.OverloadSimplifier (
    OverloadSimplifier (..),
    InjectedOverloadPair (..),
    InjectedOverload (..),
    mkOverloadSimplifier,
) where

import qualified Data.Set as Set
import Kore.IndexedModule.OverloadGraph (
    OverloadGraph,
 )
import qualified Kore.IndexedModule.OverloadGraph as OverloadGraph
import Kore.Internal.ApplicationSorts (
    applicationSortsResult,
 )
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Step.Simplification.InjSimplifier (
    InjSimplifier (..),
 )
import Prelude.Kore

{- | Consists of an overload symbol and an injection from the sort
 of the symbol; the injection can miss (@Nothing@) if not needed.
-}
data InjectedOverload = InjectedOverload
    { overload :: !Symbol
    , injectionHead :: !(Maybe (Inj ()))
    }

{- | Two overload symbols and injections.
  @overloadingSymbol = (OS, \inj{sOS, stop})@
  @overloadedSymbol =  (os, \inj{sos, sinter})@
 such that @OS@ is overloading @os@ and @sinter < stop@
-}
data InjectedOverloadPair = InjectedOverloadPair
    { overloadingSymbol :: !InjectedOverload
    , overloadedSymbol :: !InjectedOverload
    }

{- | Data structure encapsulating functionality for handling overloaded
symbols during unification.
-}
data OverloadSimplifier = OverloadSimplifier
    { -- | Whether the first argument is overloading the second
      isOverloading :: Symbol -> Symbol -> Bool
    , -- | Whether the symbol is overloaded
      isOverloaded :: Symbol -> Bool
    , -- | Apply an overloading equation from right to left.
      --
      --        In general an overloading equation is of the form
      --
      --        @overloadingOp(inj{S1,S2}(X:S1)) = inj{S,S'}(overloadedOp(X:S1))@
      --
      --        This function is given an injection prototype (used for name and
      --        attributes), the @overloadingOp@ symbol and the list of children
      --        corresponding to the @overloadedOp@ symbol application (@X:S1@ in the
      --        example above).  It then injects the children appropriately to serve
      --        as arguments to @overloadingOp@ and applies @overloadingOp@ to them.
      resolveOverloading ::
        HasCallStack =>
        Inj () ->
        Symbol ->
        [TermLike RewritingVariableName] ->
        TermLike RewritingVariableName
    , -- | Find a common overload with the result sort being a subsort of the
      --        argument, if such an overload exists. Also returns the appropriate
      --        injection, if necessary.
      unifyOverloadWithinBound ::
        Inj () ->
        Symbol ->
        Symbol ->
        Sort ->
        Maybe InjectedOverload
    , -- |Find a symbol overloaded by the argument with the result sort being
      --        a subsort of the argument, if a maximum (w.r.t. overloading) such
      --        symbol exists. Also returns the appropriate injection, if necessary.
      getOverloadedWithinSort ::
        Inj () ->
        Symbol ->
        Sort ->
        Either String (Maybe InjectedOverload)
    , -- |Given symbol firstHead of sort S1 and an injection inj{S2, injTo}
      --          If there exists a (unique) maximum overloaded symbol secondHead
      --          with its result sort S2' within S2, such that there exists a common
      --          overload headUnion of firstHead and secondHead
      --          with its result sort S within injTo, then return a 'Pair' of the form
      --
      --            @((headUnion, inj{S, injTo}), (secondHead, inj{S2', S2}))@
      --
      --          where the injections can miss if they are identities.
      --
      --          If there are no overloaded symbols candidates, return @Right Nothing@
      --
      --          If there are candidates, but no maximum, throw an
      --          'errorAmbiguousOverloads' with the candidates found
      unifyOverloadWithSortWithinBound ::
        Symbol -> -- top symbol on the LHS (wrapepd in an \inj{S1, injTo})
        Inj () -> -- injection \inj{S2, injTo} wrapping the var on the RHS
        Either String (Maybe InjectedOverloadPair)
    }

{- | Builds an Overload Simplifier given a graph encoding the overload
relation and one encoding the subsort relation. The latter is needed for
'unifyOverloadWithinBound'.
-}
mkOverloadSimplifier ::
    OverloadGraph ->
    InjSimplifier ->
    OverloadSimplifier
mkOverloadSimplifier overloadGraph InjSimplifier{isOrderedInj, injectTermTo} =
    OverloadSimplifier
        { isOverloading
        , isOverloaded
        , getOverloadedWithinSort
        , resolveOverloading
        , unifyOverloadWithinBound
        , unifyOverloadWithSortWithinBound
        }
  where
    isOverloading = OverloadGraph.isOverloading overloadGraph
    isOverloaded = OverloadGraph.isOverloaded overloadGraph

    resolveOverloading ::
        HasCallStack =>
        Inj () ->
        Symbol ->
        [TermLike RewritingVariableName] ->
        TermLike RewritingVariableName
    resolveOverloading injProto overloadedHead overloadingChildren =
        mkApplySymbol overloadedHead $
            assert (length overloadedChildrenSorts == length overloadingChildren) $
                zipWith mkInj overloadingChildren overloadedChildrenSorts
      where
        mkInj = injectTermTo injProto
        overloadedChildrenSorts =
            Symbol.applicationSortsOperands (symbolSorts overloadedHead)

    unifyOverloadWithinBound ::
        Inj () -> Symbol -> Symbol -> Sort -> Maybe InjectedOverload
    unifyOverloadWithinBound injProto s1 s2 topSort =
        headMay withinBound
      where
        withinBound =
            filterOverloads injProto topSort $
                OverloadGraph.commonOverloads overloadGraph s1 s2

    unifyOverloadWithSortWithinBound ::
        Symbol -> Inj () -> Either String (Maybe InjectedOverloadPair)
    unifyOverloadWithSortWithinBound sym injProto@Inj{injFrom, injTo} =
        do
            l <- overloads
            let l' =
                    [ InjectedOverloadPair{overloadingSymbol, overloadedSymbol}
                    | (overloadingSymbol, Just overloadedSymbol) <- l
                    ]
                rightSymbol = overload . overloadedSymbol
            case findMaxOverload rightSymbol l' of
                Nothing -> return Nothing
                Just m' ->
                    if checkMaxOverload rightSymbol m' l'
                        then return (Just m')
                        else errorAmbiguousOverloads (map rightSymbol l')
      where
        overloads =
            traverse
                ( \s ->
                    getOverloadedWithinSort injProto (overload s) injFrom
                        >>= \r -> return (s, r)
                )
                overloadings
        overloadings =
            filterOverloads injProto injTo . Set.toList $
                OverloadGraph.getOverloading overloadGraph sym

    getOverloadedWithinSort ::
        Inj () ->
        Symbol ->
        Sort ->
        Either String (Maybe InjectedOverload)
    getOverloadedWithinSort injProto sym topSort
        | null overloads = Right Nothing
        | Just m <- findMaxOverload overload overloads
          , checkMaxOverload overload m overloads =
            Right (Just m)
        | otherwise = errorAmbiguousOverloads (map overload overloads)
      where
        overloads =
            filterOverloads injProto topSort . Set.toList $
                OverloadGraph.getOverloaded overloadGraph sym

    updateMaxOverload :: (a -> Symbol) -> a -> Maybe a -> Maybe a
    updateMaxOverload _ x Nothing = Just x
    updateMaxOverload f x (Just m) =
        do
            ord <- compareOverloading sm sx
            case ord of
                LT -> return x
                _ -> return m
      where
        sx = f x
        sm = f m

    findMaxOverload :: (a -> Symbol) -> [a] -> Maybe a
    findMaxOverload f = foldr (updateMaxOverload f) Nothing

    checkMaxOverload :: (a -> Symbol) -> a -> [a] -> Bool
    checkMaxOverload f m = all (isOverloadingOrEqual (f m) . f)

    isOverloadingOrEqual x y = maybe False (LT /=) (compareOverloading x y)

    filterOverloads :: Inj () -> Sort -> [Symbol] -> [InjectedOverload]
    filterOverloads injProto topSort overloads =
        overloads
            & map (\x -> (x, injProtoTop{injFrom = resultSort x}))
            & filter (isOrderedInj . snd)
            & map (uncurry InjectedOverload . fmap removeEmptyInjection)
      where
        injProtoTop = injProto{injTo = topSort}
        removeEmptyInjection inj
            | injFrom inj == injTo inj = Nothing
            | otherwise = Just inj

    resultSort :: Symbol -> Sort
    resultSort = applicationSortsResult . symbolSorts

    compareOverloading :: Symbol -> Symbol -> Maybe Ordering
    compareOverloading x y
        | x == y = Just EQ
        | x `isOverloading` y = Just GT
        | y `isOverloading` x = Just LT
        | otherwise = Nothing

errorAmbiguousOverloads :: [Symbol] -> Either String a
errorAmbiguousOverloads overloads =
    Left
        ( "Overloaded symbols -> cannot compute maximum: "
            <> show overloads
        )
