{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}
module Kore.Step.Simplification.OverloadSimplifier
    ( OverloadSimplifier (..)
    , mkOverloadSimplifier
    ) where

import Prelude.Kore

import qualified Data.Set as Set

import Kore.IndexedModule.OverloadGraph
    ( OverloadGraph
    )
import qualified Kore.IndexedModule.OverloadGraph as OverloadGraph
import Kore.Internal.ApplicationSorts
    ( applicationSortsResult
    )
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike
import Kore.Step.Simplification.InjSimplifier
    ( InjSimplifier (..)
    )
import Pair

{- | Data structure encapsulating functionality for handling overloaded
symbols during unification.
-}
data OverloadSimplifier =
    OverloadSimplifier
        { isOverloading :: Symbol -> Symbol -> Bool
        -- ^ Whether the first argument is overloading the second
        , isOverloaded :: Symbol -> Bool
        -- ^ Whether the symbol is overloaded
        , resolveOverloading
            :: forall variable
            .  HasCallStack
            => InternalVariable variable
            => Inj ()
            -> Symbol
            -> [TermLike variable]
            -> TermLike variable
        {- ^ Apply an overloading equation from right to left.

        In general an overloading equation is of the form

        @overloadingOp(inj{S1,S2}(X:S1)) = inj{S,S'}(overloadedOp(X:S1))@

        This function is given an injection prototype (used for name and
        attributes), the @overloadingOp@ symbol and the list of children
        corresponding to the @overloadedOp@ symbol application (@X:S1@ in the
        example above).  It then injects the children appropriately to serve
        as arguments to @overloadingOp@ and applies @overloadingOp@ to them.
        -}
        , unifyOverloadWithinBound
            :: Inj ()
            -> Symbol
            -> Symbol
            -> Sort
            -> Maybe (Symbol, Maybe (Inj ()))
        {- ^ Find a common overload with the result sort being a subsort of the
        argument, if such an overload exists. Also returns the appropriate
        injection, if necessary.
        -}
        , getOverloadedWithinSort
            :: Inj ()
            -> Symbol
            -> Sort
            -> Either String (Maybe (Symbol, Maybe (Inj ())))
        {- ^Find a symbol overloaded by the argument with the result sort being
        a subsort of the argument, if a maximum (w.r.t. overloading) such
        symbol exists. Also returns the appropriate injection, if necessary.
        -}
        , unifyOverloadWithSortWithinBound
            :: Symbol
            -> Inj ()
            -> Either String (Maybe (Pair (Symbol, Maybe (Inj ()))))
        {- Given symbol firstHead of sort S1 and an injection inj{S2, injTo}
          If there exists a (unique) maximum overloaded symbol secondHead
          with its result sort S2' within S2, such that there exists a common
          overload headUnion of firstHead and secondHead
          with its result sort S within injTo, then return a 'Pair' of the form

            @((headUnion, inj{S, injTo}), (secondHead, inj{S2', S2}))@

          where the injections can miss if they are identities.

          If there are no overloaded symbols candidates, return @Right Nothing@

          If there are candidates, but no maximum, throw an
          'errorAmbiguousOverloads' with the candidates found
        -}
        }

{- | Builds an Overload Simplifier given a graph encoding the overload
relation and one encoding the subsort relation. The latter is needed for
'unifyOverloadWithinBound'.
-}
mkOverloadSimplifier
    :: OverloadGraph
    -> InjSimplifier
    -> OverloadSimplifier
mkOverloadSimplifier overloadGraph InjSimplifier {isOrderedInj, injectTermTo} =
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

    resolveOverloading
        :: forall variable
        .  HasCallStack
        => InternalVariable variable
        => Inj ()
        -> Symbol
        -> [TermLike variable]
        -> TermLike variable
    resolveOverloading injProto overloadedHead overloadingChildren =
        mkApplySymbol overloadedHead
        $ assert (length overloadedChildrenSorts == length overloadingChildren)
        $ zipWith mkInj overloadingChildren overloadedChildrenSorts
      where
        mkInj = injectTermTo injProto
        overloadedChildrenSorts =
            Symbol.applicationSortsOperands (symbolSorts overloadedHead)

    unifyOverloadWithinBound injProto s1 s2 topSort =
        headMay withinBound
      where
        withinBound =
            filterOverloads injProto topSort
            $ OverloadGraph.commonOverloads overloadGraph s1 s2

    unifyOverloadWithSortWithinBound
        :: Symbol
        -> Inj ()
        -> Either String (Maybe (Pair (Symbol, Maybe (Inj ()))))
    unifyOverloadWithSortWithinBound sym injProto@Inj { injFrom, injTo } =
        case overloads of
            Left err -> Left err
            Right l ->
                let l' =
                        [ Pair (s, inj) (s', inj')
                        | (s, inj, Just (s', inj')) <- l
                        ]
                    third (Pair _ (s, _)) = s
                    mm' = findMaxOverload third l'
                in case mm' of
                    Nothing -> Right Nothing
                    Just m' ->
                        if checkMaxOverload third m' l'
                            then Right (Just m')
                            else errorAmbiguousOverloads (map third l')

      where
        overloads =
            traverse ( \(s,inj) ->
                getOverloadedWithinSort injProto s injFrom >>=
                  \r -> return (s, inj, r)
                )
                overloadings
        overloadings =
            filterOverloads injProto injTo . Set.toList
            $ OverloadGraph.getOverloading overloadGraph sym

    getOverloadedWithinSort
        :: Inj ()
        -> Symbol
        -> Sort
        -> Either String (Maybe (Symbol, Maybe (Inj ())))
    getOverloadedWithinSort injProto sym topSort
        | null overloads = Right Nothing
        | Just m <- findMaxOverload fst overloads
        , checkMaxOverload fst m overloads
        = Right (Just m)
        | otherwise = errorAmbiguousOverloads (map fst overloads)
      where
        overloads =
            filterOverloads injProto topSort . Set.toList
            $ OverloadGraph.getOverloaded overloadGraph sym

    updateMaxOverload :: (a -> Symbol) -> a -> Maybe a -> Maybe a
    updateMaxOverload _ x Nothing = Just x
    updateMaxOverload f x (Just m)
      = do
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
    checkMaxOverload f m = all (isOverloadingOrEqual (f m) .f)

    isOverloadingOrEqual x y = maybe False (LT /=) (compareOverloading x y)

    filterOverloads
      :: Inj ()
      -> Sort
      -> [Symbol]
      -> [(Symbol, Maybe (Inj ()))]
    filterOverloads injProto topSort overloads =
        overloads
        & map (\x -> (x, injProtoTop { injFrom = resultSort x }))
        & filter (isOrderedInj . snd)
        & map (fmap
                (\inj ->
                    if injFrom inj == injTo inj then Nothing else Just inj
                )
            )
      where
        injProtoTop = injProto { injTo = topSort }

    resultSort :: Symbol -> Sort
    resultSort = applicationSortsResult  . symbolSorts
    
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
